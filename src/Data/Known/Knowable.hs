{-# LANGUAGE UndecidableInstances #-}
-- | Generalization of the `GHC.TypeList.KnownSymbol` pattern under a unified class that also covers homogeneous type-level lists.
module Data.Known.Knowable where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (..))
import qualified Data.Typeable as Tpbl
import qualified GHC.TypeLits as T

-- * The Known Class

-- | A constraint on a kind, saying types of that kind can be known.
class Knowable k where
  -- | The type of the values that corrispond to types of this kind, /e.g./ @ValType Symbol = String@.
  type ValType k :: Type
  -- | The corrisponding constraint on a type of this kind that says it's known, /e.g./ `GHC.TypeList.KnownSymbol`.
  type Known' k :: k -> Constraint
  -- | The function used to get the value corrisponding to a known type of this kind, /e.g./ `GHC.TypeList.symbolVal`.
  pToValue :: (Known k v) => Proxy v -> ValType k -- todo: simplify type signature

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

instance Knowable () where
  type ValType () = ()
  type Known' () = KnownUnit
  pToValue = unitVal

instance (Knowable k) => Knowable [k] where
  type ValType [k] = [ValType k]
  type Known' [k] = KnownList
  pToValue (_ :: Proxy (ts :: [k])) = case tySpine @k @ts of
    TyNil -> []
    (TyCons h tl) -> pToValue h : pToValue tl

-- | Generalizes `GHC.TypeList.KnownSymbol`, `GHC.TypeList.KnownNat`, and `GHC.TypeList.KnownChar`.
--   (The additional `Tpbl.Typeable` constraints are useful for debugging, but may go away in later versions.)
type Known k (a :: k) = (Known' k a, Tpbl.Typeable a, Tpbl.Typeable (ValType k))

-- | When one of the roles of values of a type is to carry type-level information,
--   this class lets us pick out that information in a general way.
class Proxies f v | f -> v where
  proxy :: f -> Proxy v

instance Proxies (Proxy v) v where
  proxy = id

-- | Generalizes `GHC.TypeList.symbolVal`, `GHC.TypeList.natVal`, and `GHC.TypeList.charVal`.
toValue :: (Knowable k, Known k v, Proxies f v) => f -> ValType k
toValue = pToValue . proxy


-- * Known Lists

-- | Term-level markers of the structure of a type-level list.
--   Pattern matching on them recovers both the spine of the list and
--   (if the list is non-empty)
--   `Known` constaint satisfactions for the head and tail.
--   This context is typically retrieved by pattern-matching.
data TySpine (ts :: [k]) where
  TyCons :: (Known k head, Known [k] tail)
         => Proxy head
         -- ^ The list has a head, which is `Known`.
         -> Proxy tail
         -- ^ The list has a tail, whick is `Known`.
         -> TySpine (head ': tail)
  -- | The list is empty.
  TyNil :: TySpine '[] -- todo: make k explicit and applyable.

-- | The type-level-list version of `GHC.TypeList.KnownSymbol`.
--   Denotes that both the spine of the list and each of its elements is known.
--   This knowlege is typically recovered by recursively pattern-matching on @tySpine \@ts@.
class (Knowable v) => KnownList (ts :: [v]) where
  -- | Pattern matching on @tySpine \@ts@ will normally have two cases, for when @ts@ is empty or not.
  --   Contextual knowledge may let one or the other case be skipped.
  --   Within those cases, the knowledge afforded by `tySpine`'s constructors can be used.
  tySpine :: TySpine ts

instance (Knowable k) => KnownList ('[] :: [k]) where
  tySpine = TyNil

instance (Known k t, Known [k] ts) => KnownList (t ': ts) where
  tySpine = TyCons Proxy Proxy

-- | Get the length of a known type-level list.
knownLength :: forall {v} (vs :: [v]) p. (KnownList vs, Proxies p vs) => p -> Int
knownLength _ = case tySpine @v @vs of
  TyNil -> 0
  TyCons _ ts -> 1 + knownLength ts

-- | Get a list of runtime type-representations for a known type-level list.
--   This is mostly for display purposes; this library may drop the use of `TypeRep`, and logic shouldn't depend on it.
typeReps :: forall {v} (vs :: [v]) p. (KnownList vs, Proxies p vs) => p -> [Tpbl.TypeRep]
typeReps _ = case tySpine @v @vs of
  TyNil -> []
  TyCons h ts -> Tpbl.typeRep h : typeReps ts


-- * Known Unit

-- | I see no reason for this not to exist too.
class KnownUnit (u :: ()) where
  unitVal :: Proxy u -> ()
instance KnownUnit '() where
  unitVal _ = ()
