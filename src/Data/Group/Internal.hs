{-# LANGUAGE TypeOperators #-}
{-# language FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Group.Internal
( FunctorWithIndex(..)
) where


import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Sum
import Data.HashMap.Lazy as HashMap
import Data.IntMap as IntMap
import Data.List.NonEmpty
import Data.Map as Map
import Data.Proxy
import Data.Sequence
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Void
import Data.Functor.Compose
import Data.Tree
import Control.Applicative


import GHC.Generics

-- | A 'Functor' with an additional index.
--
-- Instances must satisfy a modified form of the 'Functor' laws:
--
-- @
-- 'imap' f '.' 'imap' g ≡ 'imap' (\\i -> f i '.' g i)
-- 'imap' (\\_ a -> a) ≡ 'id'
-- @
class Functor f => FunctorWithIndex i f | f -> i where
  -- | Map with access to the index.
  imap :: (i -> a -> b) -> f a -> f b
  {-# minimal imap #-}

instance FunctorWithIndex () Identity where
  imap f (Identity a) = Identity (f () a)
  {-# INLINE imap #-}

instance FunctorWithIndex Void (Const e) where
  imap _ (Const a) = Const a
  {-# INLINE imap #-}

instance FunctorWithIndex k ((,) k) where
  imap f (k,a) = (k, f k a)
  {-# INLINE imap #-}

-- | The position in the list is available as the index.
instance FunctorWithIndex Int [] where
  imap f = go 0 where
    go i (a:as) = f i a : go (succ i) as
    go _ [] = []

-- | Same instance as for @[]@.
instance FunctorWithIndex Int ZipList where
  imap f = ZipList . imap f . getZipList

instance FunctorWithIndex Int NonEmpty where
  imap f = go 0 where
    go i (a :| as) = f i a :| imap f as

instance FunctorWithIndex () Maybe where
  imap f = fmap (f ())
  {-# INLINE imap #-}

-- | The position in the 'Seq' is available as the index.
instance FunctorWithIndex Int Seq where
  imap = mapWithIndex

instance FunctorWithIndex Int Vector where
  imap = V.imap
  {-# INLINE imap #-}

instance FunctorWithIndex Int IntMap where
  imap = IntMap.mapWithKey

instance FunctorWithIndex k (Map k) where
  imap = Map.mapWithKey

instance FunctorWithIndex k (HashMap k) where
  imap = HashMap.mapWithKey

instance FunctorWithIndex r ((->) r) where
  imap f g x = f x (g x)
  {-# INLINE imap #-}

instance (FunctorWithIndex i f, FunctorWithIndex j g) => FunctorWithIndex (i, j) (Compose f g) where
  imap f (Compose fg) = Compose $ imap (\k -> imap (f . (,) k)) fg
  {-# INLINE imap #-}

instance (FunctorWithIndex i f, FunctorWithIndex j g) => FunctorWithIndex (Either i j) (Sum f g) where
  imap q (InL fa) = InL (imap (q . Left)  fa)
  imap q (InR ga) = InR (imap (q . Right) ga)
  {-# INLINE imap #-}

instance (FunctorWithIndex i f, FunctorWithIndex j g) => FunctorWithIndex (Either i j) (Product f g) where
  imap f (Pair a b) = Pair (imap (f . Left) a) (imap (f . Right) b)
  {-# INLINE imap #-}

instance FunctorWithIndex [Int] Tree where
  imap f (Node a as) = Node (f [] a) $ imap (\i -> imap (f . (:) i)) as
  {-# INLINE imap #-}

instance FunctorWithIndex Void Proxy where
  imap _ Proxy = Proxy
  {-# INLINE imap #-}

instance FunctorWithIndex Void V1 where
  imap _ v = v `seq` undefined
  {-# INLINE imap #-}

instance FunctorWithIndex Void U1 where
  imap _ U1 = U1
  {-# INLINE imap #-}

instance FunctorWithIndex () Par1 where
  imap f = fmap (f ())
  {-# INLINE imap #-}

instance (FunctorWithIndex i f, FunctorWithIndex j g) => FunctorWithIndex (i, j) (f :.: g) where
  imap q (Comp1 fga) = Comp1 (imap (\k -> imap (q . (,) k)) fga)
  {-# INLINE imap #-}

instance (FunctorWithIndex i f, FunctorWithIndex j g) => FunctorWithIndex (Either i j) (f :*: g) where
  imap q (fa :*: ga) = imap (q . Left) fa :*: imap (q . Right) ga
  {-# INLINE imap #-}

instance (FunctorWithIndex i f, FunctorWithIndex j g) => FunctorWithIndex (Either i j) (f :+: g) where
  imap q (L1 fa) = L1 (imap (q . Left) fa)
  imap q (R1 ga) = R1 (imap (q . Right) ga)
  {-# INLINE imap #-}

instance FunctorWithIndex i f => FunctorWithIndex i (Rec1 f) where
  imap q (Rec1 f) = Rec1 (imap q f)
  {-# INLINE imap #-}

instance FunctorWithIndex Void (K1 i c) where
  imap _ (K1 c) = K1 c
  {-# INLINE imap #-}
