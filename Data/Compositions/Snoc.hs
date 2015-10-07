{-# LANGUAGE DeriveFunctor, CPP, Trustworthy, GeneralizedNewtypeDeriving #-}
-- | A Compositions list module biased to snoccing, rather than to consing.
--   Internally implemented the same way, just storing all elements in reverse.
--
--   See "Data.Compositions.Internal" for gory implementation, and "Data.Compositions" for the regular cons version.
module Data.Compositions.Snoc
       ( -- * Definition
         Compositions
         -- * Construction
       , singleton
       , snoc
       , fromList
         -- * Splitting
       , take
       , drop
       , splitAt
         -- * Composition
       , composed
       , dropComposed
         -- * Other
       , length
       , unsafeMap
       ) where

import qualified Data.Compositions as C
import Prelude hiding (sum, drop, take, length, concatMap, splitAt)
import Data.Monoid
#if __GLASGOW_HASKELL__ == 708
import Data.Foldable
#endif
#if __GLASGOW_HASKELL__ >= 710
import Data.Foldable hiding (length)
#endif

{-# RULES
 "drop/composed" [~2] forall n xs. composed (drop n xs) = dropComposed n xs
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

newtype Flip a = Flip { unflip :: a } deriving (Functor, Eq)

instance Monoid a => Monoid (Flip a) where
  mempty = Flip mempty
  mappend (Flip a) (Flip b) = Flip (mappend b a)

-- | A /compositions list/ or /composition tree/ is a list data type
-- where the elements are monoids, and the 'mconcat' of any contiguous sublist can be
-- computed in logarithmic time.
-- A common use case of this type is in a wiki, version control system, or collaborative editor, where each change
-- or delta would be stored in a list, and it is sometimes necessary to compute the composed delta between any two versions.
--
-- This version of a composition list is strictly biased to left-associativity, in that we only support efficient snoccing
-- to the end of the list. This also means that the 'drop' operation can be inefficient. The append operation @a <> b@
-- performs O(b log (a + b)) element compositions, so you want the right-hand list @b@ to be as small as possible.
--
-- For a version biased to consing, see "Data.Compositions". This gives the opposite performance characteristics,
-- where 'take' is slow and 'drop' is fast.
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
newtype Compositions a = C { unC :: C.Compositions (Flip a) } deriving (Eq)

instance Monoid a => Monoid (Compositions a) where
  mempty = C mempty
  mappend (C a) (C b) = C $ b <> a

instance Foldable Compositions where
  foldMap f (C x) = foldMap (f . unflip) . reverse $ toList x

instance Show a => Show (Compositions a) where
  show ls = "fromList " ++ show (toList ls)

instance (Monoid a, Read a) => Read (Compositions a) where
  readsPrec _  ('f':'r':'o':'m':'L':'i':'s':'t':' ':r) = map (\(a,s) -> (fromList a, s)) $ reads r
  readsPrec _  _ = []

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
fromList = C . C.fromList . map Flip . reverse

-- | Construct a compositions list containing just one element.
--
-- prop> \(x :: Element) -> singleton x == snoc mempty x
-- prop> \(x :: Element) -> composed (singleton x) == x
-- prop> \(x :: Element) -> length (singleton x) == 1
--
-- __Refinement of singleton lists__:
--
-- prop> \(x :: Element) -> toList (singleton x) == [x]
-- prop> \(x :: Element) -> singleton x == fromList [x]
singleton :: Monoid a => a -> Compositions a
singleton = C . C.singleton . Flip

-- | Only valid if the function given is a monoid morphism 
--
--   Otherwise, use @fromList . map f . toList@ (which is much slower).
unsafeMap :: (a -> b) -> Compositions a -> Compositions b
unsafeMap f = C . C.unsafeMap (fmap f) . unC

-- | Return the compositions list with the first /k/ elements removed.
--   In the worst case, performs __O(k log k)__ element compositions,
--   in order to maintain the left-associative bias. If you wish to run 'composed'
--   on the result of 'drop', use 'dropComposed' for better performance.
--   Rewrite @RULES@ are provided for compilers which support them.
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
drop i (C x) = C $ C.take (C.length x - i) x

-- | Return the compositions list containing only the first /k/ elements
--   of the input, in O(log k) time.
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
--  prop> \(Compositions l) (Positive n) -> take n l <> drop n l == l
take :: Monoid a => Int -> Compositions a -> Compositions a
take i (C x) = C $ C.drop (C.length x - i) x


-- | Returns the composition of the list with the first /k/ elements removed, doing only O(log k) compositions.
-- Faster than simply using 'drop' and then 'composed' separately.
--
-- prop> \(Compositions l) n -> dropComposed n l == composed (drop n l)
-- prop> \(Compositions l) -> dropComposed 0 l == composed l
dropComposed :: Monoid a => Int -> Compositions a -> a
dropComposed i (C x) = unflip $ C.takeComposed (C.length x - i) x

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
composed = unflip . C.composed . unC

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
length = C.length . unC

-- | Add a new element to the end of a compositions list. Performs O(log n) element compositions.
--
-- prop> \(x :: Element) (Compositions xs) -> snoc xs x == xs <> singleton x
-- prop> \(x :: Element) (Compositions xs) -> length (snoc xs x) == length xs + 1
--
-- __Refinement of List snoc__:
--
-- prop> \(x :: Element) (xs :: [Element]) -> snoc (fromList xs) x == fromList (xs ++ [x])
-- prop> \(x :: Element) (Compositions xs) -> toList (snoc xs x) == toList xs ++ [x]
snoc :: Monoid a => Compositions a -> a -> Compositions a
snoc (C xs) x = C (C.cons (Flip x) xs)
