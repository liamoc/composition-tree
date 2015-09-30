{-# LANGUAGE DeriveFunctor, CPP, Trustworthy #-}
{-# OPTIONS -fno-warn-missing-signatures #-}
-- | See "Data.Compositions" for normal day-to-day use. This module contains the implementation of that module.
module Data.Compositions.Internal where
import Data.Monoid
#if __GLASGOW_HASKELL__ == 708
import Data.Foldable
#else
import Data.Foldable hiding (length, sum)
#fi
import Prelude hiding (sum, drop, take, length, concatMap, splitAt)

{-# RULES
"take/composed" [~2] forall n xs. composed (take n xs) = takeComposed n xs
  #-}
-- $setup
-- >>> :set -XScopedTypeVariables
-- >>> import Control.Applicative
-- >>> import Test.QuickCheck
-- >>> import qualified Data.List as List
-- >>> type Element = [Int]
-- >>> newtype C = Compositions (Compositions Element) deriving (Show, Eq)
-- >>> instance (Monoid a, Arbitrary a) => Arbitrary (Compositions a) where arbitrary = fromList <$> arbitrary
-- >>> instance Arbitrary C where arbitrary = Compositions <$> arbitrary

-- | Returns true if the given tree is appropriately right-biased.
-- Used for the following internal debugging tests:
--
-- prop> \(Compositions l) -> wellformed l
-- prop> wellformed (mempty :: Compositions Element)
-- prop> \(Compositions a) (Compositions b) -> wellformed (a <> b)
-- prop> \(Compositions t) n -> wellformed (take n t)
-- prop> \(Compositions t) n -> wellformed (drop n t)
wellformed :: (Monoid a, Eq a) => Compositions a -> Bool
wellformed = go 1 . unwrap
  where
    go _ [] = True
    go m (x : xs) = let s = nodeSize x in s >= m && wellformedNode s x && go (s * 2) xs

    wellformedNode 1 (Node 1 Nothing _) = True
    wellformedNode n (Node n' (Just (l,r)) v) | n == n'
                   = wellformedNode (n `div` 2) l 
                     && v == nodeValue l <> nodeValue r
                     && wellformedNode (n `div` 2) r
    wellformedNode _ _ = False


-- | A /compositions list/ or /composition tree/ is a list data type
-- where the elements are monoids, and the 'mconcat' of any contiguous sublist can be
-- computed in logarithmic time.
-- A common use case of this type is in a wiki, version control system, or collaborative editor, where each change
-- or delta would be stored in a list, and it is sometimes necessary to compute the composed delta between any two versions.
--
-- This version of a composition list is strictly biased to right-associativity, in that we only support efficient consing
-- to the front of the list. This also means that the 'take' operation can be inefficient. The append operation @a <> b@
-- performs O(a log (a + b)) element compositions, so you want
-- the left-hand list @a@ to be as small as possible.
--
-- __Monoid laws:__
--
-- prop> \(Compositions l) -> mempty <> l == l
-- prop> \(Compositions l) -> l <> mempty == l
-- prop> \(Compositions t) (Compositions u) (Compositions v) -> t <> (u <> v) == (t <> u) <> v
--
-- __'toList' is monoid morphism__:
--
-- prop> toList (mempty :: Compositions Element) == []
-- prop> \(Compositions a) (Compositions b) -> toList (a <> b) == toList a ++ toList b
--
newtype Compositions a = Tree { unwrap :: [Node a] } deriving (Eq)

instance Show a => Show (Compositions a) where
  show ls = "fromList " ++ show (toList ls)

instance (Monoid a, Read a) => Read (Compositions a) where
  readsPrec _  ('f':'r':'o':'m':'L':'i':'s':'t':' ':r) = map (\(a,s) -> (fromList a, s)) $ reads r
  readsPrec _  _ = []

data Node a = Node { nodeSize :: Int
                   , nodeChildren :: Maybe (Node a , Node a)
                   , nodeValue :: !a
                   } deriving (Show, Eq, Functor)

instance (Monoid a) => Monoid (Compositions a) where
  mempty  = Tree []
  mappend (Tree a) (Tree b) = Tree (go (reverse a) b)
    where
      go [] ys  = ys
      go ( x : xs) [] = go xs [x]
      go ( x@(Node sx cx vx) : xs) ( y@(Node sy _ vy) : ys)
       = case compare sx sy of
           LT -> go xs (x : y : ys)
           GT -> let Just (l, r) = cx in go (r : l : xs) (y : ys)
           EQ -> go (Node (sx + sy) (Just (x, y)) (vx <> vy)  : xs) ys

instance Foldable Compositions where
  foldMap f = foldMap f . concatMap helper . unwrap
    where helper :: Node a -> [a]
          helper (Node _ Nothing x) = [x]
          helper (Node _ (Just (l,r)) _) = helper l ++ helper r


-- | Only valid if the function given is a monoid morphism 
--
--   Otherwise, use @fromList . map f . toList@ (which is much slower).
unsafeMap :: (a -> b) -> Compositions a -> Compositions b
unsafeMap f = Tree . fmap (fmap f) . unwrap

-- | Return the compositions list with the first /k/ elements removed, in O(log k) time.
--
-- prop> \(Compositions l) (Positive n) (Positive m) -> drop n (drop m l) == drop m (drop n l)
-- prop> \(Compositions l) (Positive n) (Positive m) -> drop n (drop m l) == drop (m + n) l
-- prop> \(Compositions l) (Positive n) -> length (drop n l) == max (length l - n) 0
-- prop> \(Compositions t) (Compositions u) -> drop (length t) (t <> u) == u
-- prop> \(Compositions l) -> drop 0 l == l
-- prop> \n -> drop n (mempty :: Compositions Element) == mempty
--
-- __Refinement of 'Data.List.drop'__:
--
-- prop> \(l :: [Element]) n -> drop n (fromList l) == fromList (List.drop n l)
-- prop> \(Compositions l) n -> toList (drop n l) == List.drop n (toList l)
drop :: Monoid a => Int -> Compositions a -> Compositions a
drop i = Tree . go i . unwrap
  where go n xs | n <= 0 = xs
        go _ [] = []
        go n (Node s c _ : r') = case compare n s of
           LT -> let Just (l , r) = c in go n (l : r : r')
           _  -> go (n - s) r'

-- | Return the compositions list containing only the first /k/ elements
--   of the input. In the worst case, performs __O(k log k)__ element compositions,
--   in order to maintain the right-associative bias. If you wish to run 'composed'
--   on the result of 'take', use 'takeComposed' for better performance.
--   Rewrite @RULES@ are provided for compilers which support them.
--
--
--  prop> \(Compositions l) (Positive n) (Positive m) -> take n (take m l) == take m (take n l)
--  prop> \(Compositions l) (Positive n) (Positive m) -> take m (take n l) == take (m `min` n) l
--  prop> \(Compositions l) (Positive n) -> length (take n l) == min (length l) n
--  prop> \(Compositions l) -> take (length l) l == l
--  prop> \(Compositions l) (Positive n) -> take (length l + n) l == l
--  prop> \(Positive n) -> take n (mempty :: Compositions Element) == mempty
--
--  __Refinement of 'Data.List.take'__:
--
--  prop> \(l :: [Element]) n -> take n (fromList l) == fromList (List.take n l)
--  prop> \(Compositions l) n -> toList (take n l) == List.take n (toList l)
--
take :: Monoid a => Int -> Compositions a -> Compositions a
take i = go i . unwrap
  where go n _  | n <= 0 = mempty
        go _ []          = mempty
        go n (x@(Node s c _) : r') = case compare n s of
           LT -> let Just (l, r) = c in go n (l : r : r')
           _  -> Tree [x] <> go (n - s) r'

-- | Returns the composition of the first /k/ elements of the compositions list, doing only O(log k) compositions.
-- Faster than simply using 'take' and then 'composed' separately.
--
-- prop> \(Compositions l) n -> takeComposed n l == composed (take n l)
-- prop> \(Compositions l) -> takeComposed (length l) l == composed l
--
-- prop> \(Compositions l) (Positive n) -> take n l <> drop n l == l
takeComposed :: Monoid a => Int -> Compositions a -> a
takeComposed i = go i . unwrap
  where go n _ | n <= 0 = mempty
        go _ []         = mempty
        go n (Node s c v : r') = case compare n s of
          LT -> let Just (l , r) = c in go n (l : r : r')
          _  -> v <> go (n - s) r'

-- | A convenience alias for 'take' and 'drop'
--
-- prop> \(Compositions l) i -> splitAt i l == (take i l, drop i l)
{-# INLINE splitAt #-}
splitAt :: Monoid a => Int -> Compositions a -> (Compositions a, Compositions a)
splitAt i c = (take i c, drop i c)


-- | Compose every element in the compositions list. Performs only
-- O(log n) compositions.
--
-- __Refinement of 'mconcat'__:
--
-- prop> \(l :: [Element]) -> composed (fromList l) == mconcat l
-- prop> \(Compositions l) -> composed l == mconcat (toList l)
--
-- __Is a monoid morphism__:
--
-- prop> \(Compositions a) (Compositions b) -> composed (a <> b) == composed a <> composed b
-- prop> composed mempty == (mempty :: Element)
{-# INLINE[2] composed #-}
composed :: Monoid a => Compositions a -> a
composed = mconcat . map nodeValue . unwrap

-- | Construct a compositions list containing just one element.
--
-- prop> \(x :: Element) -> singleton x == cons x mempty
-- prop> \(x :: Element) -> composed (singleton x) == x
-- prop> \(x :: Element) -> length (singleton x) == 1
--
-- __Refinement of singleton lists__:
--
-- prop> \(x :: Element) -> toList (singleton x) == [x]
-- prop> \(x :: Element) -> singleton x == fromList [x]
singleton :: Monoid a => a -> Compositions a
singleton = Tree . (:[]) . Node 1 Nothing

-- | Get the number of elements in the compositions list, in O(log n) time.
--
-- __Is a monoid morphism__:
--
-- prop> length (mempty :: Compositions Element) == 0
-- prop> \(Compositions a) (Compositions b) -> length (a <> b) == length a + length b
--
-- __Refinement of 'Data.List.length'__:
--
-- prop> \(x :: [Element]) -> length (fromList x) == List.length x
-- prop> \(Compositions x) -> length x == List.length (toList x)
length :: Compositions a -> Int
length (Tree l) = sum (map nodeSize l)

-- | Convert a compositions list into a list of elements. The other direction
--   is provided in the 'Data.Foldable.Foldable' instance. This will perform O(n log n) element compositions.
--
-- __Isomorphism to lists__:
--
-- prop> \(Compositions x) -> fromList (toList x) == x
-- prop> \(x :: [Element]) -> toList (fromList x) == x
--
-- __Is monoid morphism__:
--
-- prop> fromList ([] :: [Element]) == mempty
-- prop> \(a :: [Element]) b -> fromList (a ++ b) == fromList a <> fromList b
fromList :: Monoid a => [a] -> Compositions a
fromList = mconcat . map singleton

-- | Add a new element to the front of a compositions list. Performs O(log n) element compositions.
--
-- prop> \(x :: Element) (Compositions xs) -> cons x xs == singleton x <> xs
-- prop> \(x :: Element) (Compositions xs) -> length (cons x xs) == length xs + 1
--
-- __Refinement of List @(:)@__:
--
-- prop> \(x :: Element) (xs :: [Element]) -> cons x (fromList xs) == fromList (x : xs)
-- prop> \(x :: Element) (Compositions xs) -> toList (cons x xs) == x : toList xs
cons :: Show a => Monoid a => a -> Compositions a -> Compositions a
cons x = (singleton x <>)
