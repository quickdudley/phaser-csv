{-# LANGUAGE GADTs, LambdaCase, ScopedTypeVariables #-}
module Codec.Phaser.CSV (
  ByHeader,
  column,
  optColumn,
  stringRow,
  byHeader,
 ) where

import Codec.Phaser
import Codec.Phaser.Core (eof, fromAutomaton)
import Control.Applicative
import Data.Char
import Data.Foldable
import Data.List (intercalate)

inlineSpace :: Char -> Bool
inlineSpace = (&&) <$> isSpace <*> (/= '\n')

stringCell :: Monoid p => Phase p Char o String
stringCell = fromAutomaton $ cell >># many get

cell :: Monoid p => Phase p Char Char ()
cell = (<|> eof) $ get >>= \case
  '\"' -> goq
  ',' -> put1 ','
  '\n' -> put1 '\n'
  c
    | inlineSpace c -> cell
    | otherwise -> yield c *> gouq
 where
  goq = get >>= \case
    '\"' -> cqq
    c -> yield c *> goq
  gouq = (<|> eof) $ get >>= \case
    ',' -> put1 ','
    '\n' -> put1 '\n'
    c
      | isSpace c -> gouqs (c:)
      | otherwise -> yield c *> gouq
  cqq = get >>= \case
    '\"' -> yield '\"' *> goq
    c -> ((() <$) $ put1 c *> munch inlineSpace)
  gouqs acc = (<|> eof) $ get >>= \case
    ',' -> put1 ','
    '\n' -> put1 '\n'
    c
      | isSpace c -> gouqs (acc . (c:))
      | otherwise -> traverse yield (acc []) *>
        yield c *>
        gouq

stringRow :: Monoid p => Phase p Char o [String]
stringRow = sepBy (fromAutomaton $ cell >># many get) (char ',') <*
  (eof <|> (() <$ char '\n'))

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

byHeader :: forall p p' o o' a . (Monoid p, Monoid p') =>
  ByHeader p o a -> Phase p' Char o' (Phase p Char o a)
byHeader b = let
  ignoreCell :: Monoid p0 => Phase p0 Char o0 ()
  ignoreCell = fromAutomaton $
    cell >># let loop = (get *> loop) <|> pure () in loop
  headerCell :: Monoid p0 => Phase p0 Char o0 String
  headerCell = (<* ((() <$ char ',') <|> eof)) $ stringCell >>= \case
    "" -> "" <$ ((char ',' *> put1 ',') <|> (char '\n' *> put1 '\n'))
    h -> return h
  finishRow :: Monoid p0 => Phase p0 Char o0 ()
  finishRow = let
    loop = ((ignoreCell *> char ',' *> loop) <|> pure ())
    in loop <* (eof <|> (() <$ char '\n'))
  build (DoneH p) = Right p <$ finishRow
  build (NewH b) = (headerCell >>= \a -> case fill a b of
     Just (DoneH p) -> Right p <$ finishRow
     Just p@(Partial _ _) -> build p
     Just (NewH b') -> build (Partial (id <$ ignoreCell) b')
     _ -> build (Partial (id <$ ignoreCell) b)
   ) <|> (fin b <$ finishRow)
  build (Partial p b) = (headerCell >>= \a -> case fill a b of
    Just (DoneH p') -> Right (p <*> p') <$ finishRow
    Just (NewH z) -> build (Partial (p <* char ',' <* ignoreCell) z)
    Just (Partial p' b') -> build (Partial ((.) <$> p <*> (char ',' *> p')) b')
    Nothing -> build (Partial (p <* char ',' <* ignoreCell) b)
   ) <|> (((p <*>) <$> fin b) <$ finishRow)
  fill :: String -> ByHeader p o x -> Maybe (FHBuild p o x)
  fill h (CellH h' _ p)
    | h == h' = Just (DoneH $ fromAutomaton $ cell >># p)
  fill h (SomeH f a) = case fill h f of
    Just (DoneH p) -> Just $ Partial p a
    Just (NewH z') -> Just $ NewH (z' <*> a)
    Just (Partial p' b') -> Just $ Partial (uncurry <$> p') ((,) <$> b' <*> a)
    Nothing -> case fill h a of
      Just (DoneH p) -> Just $ Partial (flip ($) <$> p) f
      Just (NewH z') -> Just $ NewH (($) <$> f <*> z')
      Just (Partial p' b') -> Just $ Partial
        ((\f' (f'',z) -> f'' (f' z)) <$> p')
        ((,) <$> f <*> b')
      Nothing -> Nothing
  fill _ _ = Nothing
  fin :: ByHeader p o x -> Either [String] (Phase p Char o x)
  fin (CellH h Nothing _) = Left [h]
  fin (CellH _ (Just r) _) = Right (pure r)
  fin (SomeH f a) = case (fin f, fin a) of
    (Left fe, Left ae) -> Left (fe ++ ae)
    (Left e, _) -> Left e
    (_, Left e) -> Left e
    (Right a, Right b) -> Right (a <*> b)
  in build (NewH b) >>= \case
    Left e -> fail $ case e of
      [e'] -> "Required column " ++ e' ++ " is missing"
      _ -> "Required columns " ++ intercalate ", " e ++ " are missing"
    Right p -> return p

test :: Monoid p => Phase p Char o [(Integer,Integer)]
test = do
  p <- byHeader $
    (,) <$> column "a" regular <*> column "b" regular
  many p
