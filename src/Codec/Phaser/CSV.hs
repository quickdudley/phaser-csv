{-# LANGUAGE GADTs, LambdaCase, ScopedTypeVariables #-}
module Codec.Phaser.CSV (

 ) where

import Codec.Phaser
import Codec.Phaser.Core (eof, fromAutomaton)
import Control.Applicative
import Data.Char
import Data.Foldable

inlineSpace :: Char -> Bool
inlineSpace = (&&) <$> isSpace <*> (/= '\n')

cell :: Monoid p => Phase p Char Char ()
cell = (<|> eof) $ get >>= \case
  '\"' -> goq
  ',' -> put1 ','
  '\n' -> put1 '\n'
  c
    | isSpace c -> cell
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

data FromHeaders p o a where
  CellH :: String -> Phase p Char o a -> FromHeaders p o a
  SomeH :: FromHeaders p o (a -> b) -> FromHeaders p o a
    -> FromHeaders p o b
  PureH :: a -> FromHeaders p o a

instance Monoid p => Functor (FromHeaders p o) where
  fmap f (CellH h p) = CellH h (fmap f p)
  fmap f (SomeH l r) = SomeH (fmap (f .) l) r
  fmap f (PureH a) = PureH (f a)

instance Monoid p => Applicative (FromHeaders p o) where
  pure = PureH
  PureH f <*> a = fmap f a
  f <*> PureH a = fmap ($ a) f
  f <*> a = SomeH f a

data FHBuild p o a where
  NewH :: FromHeaders p o a -> FHBuild p o a
  DoneH :: Phase p Char o a -> FHBuild p o a
  Partial :: Phase p Char o (a -> b) -> FromHeaders p o a -> FHBuild p o b

fromHeaders :: forall p o a . Monoid p => [String] -> FromHeaders p o a -> Phase p Char o a
fromHeaders hs b = let
  ignoreCell :: Phase p Char o ()
  ignoreCell = fromAutomaton $
    cell >># let loop = (get *> loop) <|> pure () in loop
  build _ (DoneH p) = p <* sepBy ignoreCell (char ',')
  build [] _ = fail "Required columns are not present"
  build (a:r) (NewH b) = case fill a b of
    Just (DoneH p) -> p
    Just p@(Partial _ _) -> build r p
    Just (NewH b') -> build r (Partial (id <$ ignoreCell) b')
    _ -> build r (Partial (id <$ ignoreCell) b)
  build (a:r) (Partial p b) = case fill a b of
    Just (DoneH p') -> (p <*> p') <* sepBy ignoreCell (char ',')
    Just (NewH z) -> build r (Partial (p <* char ',' <* ignoreCell) z)
    Just (Partial p' b') -> build r (Partial ((.) <$> p <*> (char ',' *> p')) b')
    Nothing -> build r (Partial (p <* char ',' <* ignoreCell) b)
  fill :: String -> FromHeaders p o x -> Maybe (FHBuild p o x)
  fill h (CellH h' p)
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
  in build hs (NewH b)
