{-# LANGUAGE UndecidableInstances #-}
-- | Generalization of the `GHC.TypeList.KnownSymbol` pattern under a unified class that also covers homogeneous type-level lists.
module Data.Known where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import qualified Data.Typeable as Tpbl
import qualified GHC.TypeLits as T

-- * Handling type-level lists literals

-- | Term-level markers of the structure of a type-level list.
--   Pattern matching on them recovers both the spine of the list and, if applicable,
--   `Known` constaint satisfactions for the head and tail.
data TySpine (ps :: [k]) where
  -- | Denotes that the list has a head and tail.
  TyCons :: (Known k h, Known [k] ts) => Proxy h -> Proxy ts -> TySpine (h ': ts)
  -- | Denotes that the list is empty.
  TyNil :: TySpine '[]

-- | The type-level-list version of `GHC.TypeList.KnownSymbol`.
--   Denotes that both the spine of the list and each of its elements is known at compile-time.
--   This knowlege is typically recovered by recursively pattern-matching on @tySpine \@ls@.
class (Knowable v) => KnownList (ls :: [v]) where
  -- | Pattern matching on @tySpine \@ls@ will normally have two cases, for when @ls@ is empty or not.
  --   Contextual knowledge may let one or the other case be skipped.
  --   Within those cases, the knowledge afforded by `tySpine`'s constructors can be used.
  tySpine :: TySpine ls

instance (Knowable k) => KnownList ('[] :: [k]) where
  tySpine = TyNil

instance (Known k l, Known [k] ls) => KnownList (l ': ls) where
  tySpine = TyCons Proxy Proxy


class Knowable k where
  type ValType k :: Type
  type Known' k :: k -> Constraint
  pToValue :: (Known k v) => Proxy v -> ValType k

instance Knowable T.Symbol where
  type ValType T.Symbol = String
  type Known' T.Symbol = T.KnownSymbol
  pToValue = T.symbolVal

instance Knowable T.Nat where
  type ValType T.Nat = Integer
  type Known' T.Nat = T.KnownNat
  pToValue = T.natVal

instance Knowable Char where
  type ValType Char = Char
  type Known' Char = T.KnownChar
  pToValue = T.charVal

instance (Knowable k) => Knowable [k] where
  type ValType [k] = [ValType k]
  type Known' [k] = KnownList
  pToValue (_ :: Proxy (ls :: [k])) = case tySpine @k @ls of
    TyNil -> []
    (TyCons h ts) -> pToValue h : pToValue ts

type Known k (a :: k) = (Known' k a, Tpbl.Typeable a, Tpbl.Typeable (ValType k))

class Proxies f v | f -> v where
  proxy :: f -> Proxy v

instance Proxies (Proxy v) v where
  proxy = id

toValue :: (Knowable k, Known k v, Proxies f v) => f -> ValType k
toValue = pToValue . proxy

