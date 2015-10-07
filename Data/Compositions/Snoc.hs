-- | A Compositions list module biased to snoccing, rather than to consing.
--   Internally implemented the same way, just storing all elements in reverse.
--
--   See "Data.Compositions.Snoc.Internal" for gory implementation, and "Data.Compositions" for the regular cons version.
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

import Data.Compositions.Snoc.Internal
import Prelude hiding (length, take, drop, splitAt)
