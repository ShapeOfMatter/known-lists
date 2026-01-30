{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}

module Example
  ( -- * Length-indexed vectors
    VecN(..)
    ,VecU(..)
    ,indexN
    ,indexU
    ,index
    ,RaggedMatrix(..)
    ,(!!!)
    ,raggedFromList
    ,raggedToList
    ,raggedFromStdIn
  ) where


import Data.Bifunctor.Flip
import Data.Foldable (toList)
import Data.Functor.Compose (Compose (Compose))
import Data.Functor.Const (Const (Const))
import Data.Known.Knowable
import Data.Known.Membership
import Data.Known.TypeIndexed
import Data.Proxy (Proxy (..))
import qualified GHC.Exts as EXTS
import GHC.TypeLits (type (+))
import qualified GHC.TypeLits

data VecN (n :: GHC.TypeLits.Nat) a where
  NNil  :: VecN 0 a
  NCons :: a -> VecN n a -> VecN (n + 1) a
indexN :: VecN n a -> Int -> a  -- UNSAFE
indexN (NCons x xs) i | i == 0 = x
                      | 0 < i = indexN xs (i - 1)
                      | otherwise = error "indexN: Out of bounds: index was negative."
indexN NNil _ = error "indexN: Out of bounds: index was too large."

type Nat = [()]
type Fin n = Member '() n

data VecU (n :: Nat) a where
  UNil  :: VecU '[] a
  UCons :: a -> VecU n a -> VecU ('() ': n) a
indexU :: VecU n a -> Fin n -> a
indexU (UCons x _) First = x
indexU (UCons _ xs) (Later i) = indexU xs i
indexU UNil i = case i of {}  -- This index function is safe; GHC knows there is no such `i`.

type Vec (n :: Nat) a = TVec n a
index :: Vec n a -> Fin n -> a
index = (Data.Known.TypeIndexed.!)

newtype RaggedMatrix (rows :: [Nat]) a = Ragged {raggedIndexes :: TIndexed rows (Flip TVec a) }

(!!!) :: (Known Nat row) => RaggedMatrix rows a -> (Member row rows, Fin row) -> a
(!!!) (Ragged TIndexed{tindex}) (row, i) = runFlip (tindex row) ! i

raggedFromList :: forall rows a. (Known [Nat] rows) => [a] -> RaggedMatrix rows a
raggedFromList xs = case tySpine @Nat @rows of
  TyNil -> Ragged $ TIndexed \case{}
  TyCons (_ :: Proxy r1) (_ :: Proxy rows') ->
                let (xs1, xsTail) = splitAt (knownLength $ allOf @r1) xs
                    r1 :: TVec r1 a
                    r1 = EXTS.fromList $ zip (repeat ()) xs1 -- This is where it will crash if the list isn't big enough.
                    f :: TIndex rows' (Flip TVec a)
                    Ragged TIndexed{tindex=f} = raggedFromList xsTail
                in Ragged $ TIndexed \case
                    First -> Flip r1
                    Later i -> f i

raggedToList :: forall rows a. (Known [Nat] rows) => RaggedMatrix rows a -> [a]
raggedToList (Ragged (TIndexed f)) = concat lists
  where lists :: TVec rows [a]
        lists = pack (toList . runFlip . f)

raggedFromStdIn :: forall rows a. (Read a, Known [Nat] rows) => IO (RaggedMatrix rows a)
raggedFromStdIn = Ragged <$> rfsi
  where rfsi :: IO (TIndexed rows (Flip TVec a))
        rfsi = sequenceT $ TIndexed $ Compose <$> rows
        rows :: forall row. (Known Nat row) => Member row rows -> IO (Flip TVec a row)
        rows _ = Flip <$> row
        row :: forall row. (Known Nat row) => IO (TVec row a)
        row = fmap TVec $ sequenceT $ TIndexed $ Compose . fmap Const <$> item
        item :: forall i row. Member i row -> IO a
        item = const readLn
              
