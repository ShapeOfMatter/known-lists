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

-- | A data structure parameterized by a type-level list of Nats,
--   where each Nat n in the list corresponds to a Vec n a.
module Example
  ( -- * Length-indexed vectors
    VecN(..)
    ,VecU(..)
    ,indexN
    ,indexU
    ,index
    ,RaggedMatrix(..)
    ,(!!!)
    ,raggedFromTape
    ,raggedToList
    ,raggedFromStdIn
  {-, vindex
    -- * The main structure
  , NatStruct(..)
  , nsNil
  , nsCons
    -- * Re-exports for convenience
  , Member(..)
  , Finite
  , finites
  , getFinite-}
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

--------------------------------------------------------------------------------
-- Vec: A length-indexed vector
--------------------------------------------------------------------------------

data VecN (n :: GHC.TypeLits.Nat) a where
  NNil  :: VecN 0 a
  NCons :: a -> VecN n a -> VecN (n + 1) a
indexN :: VecN n a -> Int -> a  -- UNSAFE
indexN (NCons x xs) i | i == 0 = x
                      | 0 < i = indexN xs (i - 1)
                      | otherwise = error "indexN: Out of bounds: index was negative."
indexN NNil _ = error "indexN: Out of bounds: index was too large."

type Nat = [()]
type Zero = '[] :: Nat
type Suc n = '() ': n
type Fin n = Member '() n

data VecU (n :: Nat) a where
  UNil  :: VecU Zero a
  UCons :: a -> VecU n a -> VecU (Suc n) a
indexU :: VecU n a -> Fin n -> a
indexU (UCons x _) First = x
indexU (UCons _ xs) (Later i) = indexU xs i
indexU UNil i = case i of {}  -- This index function is safe; GHC knows there is no such `i`.

type Vec (n :: Nat) a = TVec n a
index :: Vec n a -> Fin n -> a
index = (Data.Known.TypeIndexed.!)

newtype RaggedMatrix (rows :: [Nat]) a = Ragged {raggedIndexes :: TIndexed rows (Flip TVec a) }

(!!!) :: (Known Nat row, Known () i) => RaggedMatrix rows a -> (Member row rows, Member i row) -> a
(!!!) (Ragged TIndexed{tindex}) (row, i) = runFlip (tindex row) ! i

raggedFromTape :: forall rows a. (Known [Nat] rows) => [a] -> RaggedMatrix rows a
raggedFromTape xs = case tySpine @Nat @rows of
  TyNil -> Ragged $ TIndexed \case{}
  TyCons (_ :: Proxy r1) (_ :: Proxy rows') ->
                let (xs1, xsTail) = splitAt (knownLength $ allOf @r1) xs
                    r1 :: TVec r1 a
                    r1 = EXTS.fromList $ zip (repeat ()) xs1 -- This is where it will crash if the list isn't big enough.
                    f :: TIndex rows' (Flip TVec a)
                    Ragged TIndexed{tindex=f} = raggedFromTape xsTail
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
              
{-
-- | A structure parameterized by a type-level list of Nats.
--   For each Nat @n@ in @ns@, the structure contains a @Vec n a@.
--
--   The key insight is that this is essentially a dependent product:
--   for each type n in ns, we store a value of type (Vec n a).
--   
--   We use a function from Member proofs to Vecs to represent this.
newtype NatStruct (ns :: [Nat]) a = NatStruct 
  { vecOfLength :: forall n. Known Nat n => Member n ns -> Vec n a }

--------------------------------------------------------------------------------
-- Constructing NatStructs
--------------------------------------------------------------------------------

-- | Construct a NatStruct for an empty list of Nats.
nsNil :: NatStruct '[] a
nsNil = NatStruct $ \case {}

-- | Cons a Vec onto a NatStruct.
--   Given a Vec of length m and a NatStruct for the remaining lengths,
--   produce a NatStruct for (m ': ns).
nsCons :: forall m ns a. Vec m a -> NatStruct ns a -> NatStruct (m ': ns) a
nsCons v (NatStruct rest) = NatStruct go
  where
    go :: forall n. KnownNat n => Member n (m ': ns) -> Vec n a
    go First     = v
    go (Later p) = rest p
-}
