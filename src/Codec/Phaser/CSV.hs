{-# LANGUAGE GADTs, LambdaCase, ScopedTypeVariables #-}
module Codec.Phaser.CSV (
  ByHeader,
  column,
  optColumn,
  byHeader,
  fromCell
 ) where

import Codec.Phaser
import Codec.Phaser.Core (PhaserType, chainWith, eof, fromAutomaton)
import Control.Applicative
import Data.Char
import Data.Foldable
import Data.List (intercalate)

inlineSpace :: Char -> Bool
inlineSpace = (&&) <$> isSpace <*> (/= '\n')

stringCell :: Monoid p => Phase p Char o String
stringCell = fromAutomaton $ cell >># many get

sepChar :: Monoid p => Phase p Char o Char
sepChar = satisfy $ (||) <$> (== ',') <*> (== '\n')

cell :: Monoid p => Phase p Char Char (Maybe Char)
cell = (<|> (Nothing <$ eof)) $ get >>= \case
  '\"' -> goq
  ',' -> pure (Just ',')
  '\n' -> pure (Just '\n')
  c
    | inlineSpace c -> cell
    | otherwise -> yield c *> gouq
 where
  goq = get >>= \case
    '\"' -> cqq
    c -> yield c *> goq
  gouq = (<|> (Nothing <$ eof)) $ get >>= \case
    ',' -> pure (Just ',')
    '\n' -> pure (Just '\n')
    c
      | isSpace c -> gouqs (c:)
      | otherwise -> yield c *> gouq
  cqq = (<|> (Nothing <$ eof)) $ get >>= \case
    '\"' -> yield '\"' *> goq
    c -> put1 c *> munch inlineSpace *>
      ((Just <$> sepChar) <|> (Nothing <$ eof))
  gouqs acc = (<|> (Nothing <$ eof)) $ get >>= \case
    ',' -> pure (Just ',')
    '\n' -> pure (Just '\n')
    c
      | isSpace c -> gouqs (acc . (c:))
      | otherwise -> traverse_ yield (acc []) *>
        yield c *>
        gouq

row :: Monoid p => Phase p Char Char Bool
row = (get >>= \case
  '\n' -> return True
  c -> yield c *> row
 ) <|> (False <$ eof)

cellwise :: Monoid p => Phase p Char String ()
cellwise = (>>= id) $ (fromAutomaton $ chainWith j cell (many get >>= yield)) where
  j Nothing _ = eof
  j (Just ',') _ = cellwise
  j (Just s) _ = put1 s

column :: String -> Phase p Char o a -> ByHeader p o a
column h p = CellH h Nothing p

optColumn :: String -> a -> Phase p Char o a -> ByHeader p o a
optColumn h d p = CellH h (Just d) p

data ByHeader p o a where
  CellH :: String -> Maybe a -> Phase p Char o a -> ByHeader p o a
  SomeH :: ByHeader p o (a -> b) -> ByHeader p o a
    -> ByHeader p o b
  PureH :: a -> ByHeader p o a

instance Monoid p => Functor (ByHeader p o) where
  fmap f (CellH h d p) = CellH h (fmap f d) (fmap f p)
  fmap f (SomeH l r) = SomeH (fmap (f .) l) r
  fmap f (PureH a) = PureH (f a)

instance Monoid p => Applicative (ByHeader p o) where
  pure = PureH
  PureH f <*> a = fmap f a
  f <*> PureH a = fmap ($ a) f
  f <*> a = SomeH f a

data FHBuild p o a where
  NewH :: ByHeader p o a -> FHBuild p o a
  DoneH :: Phase p Char o a -> FHBuild p o a
  Partial :: Phase p Char o (a -> b) -> ByHeader p o a -> FHBuild p o b

fromCell :: (PhaserType s, Monoid p) => s p Char o a -> Phase p Char o a
fromCell = (>>= id) . fromAutomaton . chainWith j cell where
  j (Just x) a = a <$ put1 x
  j Nothing a = a <$ eof

ignoreCell :: Monoid p => Phase p Char o ()
ignoreCell = (>>= id) $ fromAutomaton $ chainWith j cell loop where
  loop = (get *> loop) <|> return ()
  j Nothing _ = empty
  j (Just x) a = a <$ put1 x

byHeader :: forall p p' o o' a . (Monoid p, Monoid p') =>
  (String -> String -> Bool) -> ByHeader p o a ->
  Phase p' Char o' (Phase p Char o a)
byHeader match b0 = let
  headersDone :: Phase p' String o' ()
  headersDone = (get *> headersDone) <|> eof
  clear :: Phase p Char o ()
  clear = (get >>= \case
    '\n' -> put1 '\n'
    c -> clear
   ) <|> (eof *> put1 '\n')
  build :: FHBuild p o a -> Phase p' String o' (Phase p Char o a)
  build (NewH b) = (get >>= \h -> case step b h of
    Just (NewH b') -> build (Partial (id <$ ignoreCell) b')
    Just (DoneH p) -> return $ p <* clear
    Just (Partial p b') -> build (Partial p b')
    Nothing -> build (Partial (id <$ ignoreCell) b)
   ) <|> (tidy (fin b) <* eof)
  build (DoneH p) = (p <* clear) <$ headersDone
  build (Partial p b) = (get >>= \h -> case step b h of
    Just (NewH b') -> build $ Partial (p <* char ',' <* ignoreCell) b'
    Just (DoneH b') -> p <*> (char ',' *> b' <* clear) <$ headersDone
    Just (Partial p' b') -> build $ Partial
      ((.) <$> p <*> (char ',' *> p')) b'
    Nothing -> build $ Partial (p <* char ',' <* ignoreCell) b
   ) <|> ((p <*>) <$> (tidy $ fin b) <* eof)
  step :: ByHeader p o x -> String -> Maybe (FHBuild p o x)
  step (CellH h' _ p) h | match h' h = Just $ DoneH $ fromCell p
  step (SomeH f' a') h = case step f' h of
    Just (NewH f) -> Just (NewH $ f <*> a')
    Just (DoneH f) -> Just (Partial f a')
    Just (Partial p z) -> Just $
      Partial (flip ($) <$> p) ((flip . flip id) <$> z <*> a')
    Nothing -> case step a' h of
      Just (NewH a) -> Just (NewH $ f' <*> a)
      Just (DoneH a) -> Just (Partial (flip ($) <$> a) f')
      Just (Partial p z) -> Just $
        Partial (flip ($) <$> p) (((. flip id) . (.)) <$> f' <*> z)
      Nothing -> Nothing
  step _ _ = Nothing
  tidy :: Either [String] (Phase p Char o x) ->
    Phase p' String o' (Phase p Char o x)
  tidy (Left [e]) = fail $ "Required column " ++ e ++ " is missing"
  tidy (Left e) = fail $
    "Required columns " ++ intercalate ", " e ++ " are missing"
  tidy (Right r) = return r
  fin :: ByHeader p o x -> Either [String] (Phase p Char o x)
  fin (CellH h Nothing _) = Left [h]
  fin (CellH _ (Just r) _) = Right (pure r)
  fin (SomeH f' a') = case (fin f', fin a') of
    (Left e1, Left e2) -> Left (e1 ++ e2)
    (Left e, _) -> Left e
    (_, Left e) -> Left e
    (Right f, Right a) -> Right (f <*> a)
  fin (PureH a) = Right (pure a)
  in (<* ((() <$ char '\n') <|> eof)) $ fromAutomaton $
    cellwise >># (build (NewH b0))
