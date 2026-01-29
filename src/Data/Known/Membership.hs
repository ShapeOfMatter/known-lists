-- | Term level proofs of membership and subset relations among type-level lists.
module Data.Known.Membership where

import Data.Known.Knowable
import Data.Proxy (Proxy (..))
import qualified Data.Typeable as Tpbl

-- * Membership proofs

-- | A term-level proof that a type is a member of a list of types.
--   These are frequently used both for proofs /per se/ and as proxy-like identifers for the items in the list.
--
--   For example: @foo :: Member foo symbols@ is a proof that the type-level `Symbol`, @foo@, is in @symbols@,
--   and it can also be used as a __term-level__ identifier for the __type-level__ @foo@,
--   similar to how a @proxy@ might be used.
--
--   Pattern matching on these values is like pattern matching on a successor-based @Nat@;
--   in this sense a @Member x xs@ is an index into @xs@ at which @x@ can be found.
data Member (x :: k) (xs :: [k]) where
  First :: forall xs x xs'. (xs ~ (x ': xs')) => Member x (x ': xs')
  Later :: Member x xs -> Member x (y ': xs)
  -- todo: Eq and Ord probably are meaningful and derivable...
instance Proxies (Member x ys) x where
  proxy _ = Proxy
instance (Known k x, Known [k] xs) => Show (Member x xs) where
  show m = "Member " ++ (show . Tpbl.typeRep . proxy $ m) ++ " " ++ (show . typeReps $ Proxy @xs)

-- | Any type @t@ is a member of the list @'[t]@.
alone :: Member t (t ': '[])
alone = First

-- | Use any membership proof to to safely call code that only works on a non-empy list.
quorum1 ::
  forall {k} (ts :: [k]) (t :: k) a.
  (Known [k] ts) =>
  Member t ts ->
  -- ^ A proof that a member of `ts` exists.
  (forall head tail. (Known k head, Known [k] tail, ts ~ head ': tail) => a) ->
  -- ^ A computation that only works if `ts` isn't `'[]`.
  a
quorum1 t a = case (t, tySpine @k @ts) of
  (First, TyCons _ _) -> a
  (Later _, TyCons _ _) -> a

-- * Simple indexes as `Member` objects.
-- 
-- $listedNth
--
-- These will get depricated in favor of @Nat@ based indexing at some point.

-- | A `Member` value for the first item in a list.
--   Note that type-applicaiton is different than with `First`, to which this is otherwise redundant.
listedFirst :: forall t1 ts. Member t1 (t1 ': ts) -- Can we replace all of these with something using off-the-shelf type-level Nats?
listedFirst = First

-- | A `Member` value for the second item in a list.
listedSecond :: forall t2 t1 ts. Member t2 (t1 ': t2 ': ts)
listedSecond = inSuper (consSuper refl) listedFirst

-- | A `Member` value for the third item in a list.
listedThird :: forall t3 t2 t1 ts. Member t3 (t1 ': t2 ': t3 ': ts)
listedThird = inSuper (consSuper refl) listedSecond

-- | A `Member` value for the forth item in a list.
listedForth :: forall t4 t3 t2 t1 ts. Member t4 (t1 ': t2 ': t3 ': t4 ': ts)
listedForth = inSuper (consSuper refl) listedThird

-- | A `Member` value for the fifth item in a list.
listedFifth :: forall t5 t4 t3 t2 t1 ts. Member t5 (t1 ': t2 ': t3 ': t4 ': t5 ': ts)
listedFifth = inSuper (consSuper refl) listedForth

-- | A `Member` value for the sixth item in a list.
listedSixth :: forall t6 t5 t4 t3 t2 t1 ts. Member t6 (t1 ': t2 ': t3 ': t4 ': t5 ': t6 ': ts)
listedSixth = inSuper (consSuper refl) listedFifth

-- * Subset proofs

-- | A term level proof that one type-level list represents a subset of another,
--   embodied by a total function from proof-of-membership in the sublist to proof-of-membership in the superlist.
--   (If you make one with a partial funciton, all bets are off.)
newtype Subset xs ys = Subset
  { -- | Convert a proof of membership in the sublist to a proof of membership in the superlist.
    -- Frequently used to show that a location is part of a larger set of locations.
    inSuper :: forall x. Member x xs -> Member x ys
  }
instance Proxies (Subset xs ys) xs where
  proxy _ = Proxy
instance (Known [k] xs, Known [k] ys) => Show (Subset xs ys) where
  show _ = "Subset " ++ (show . typeReps $ Proxy @xs) ++ " " ++ (show . typeReps $ Proxy @ys)

-- | The subset relation is reflexive.
refl :: Subset xs xs
refl = Subset id

-- | Alias `refl`. When used as an identifier, this is more descriptive.
allOf :: forall ts. Subset ts ts
allOf = refl

-- | The sublist relation is transitive.
transitive :: Subset xs ys -> Subset ys zs -> Subset xs zs
transitive sxy syz = Subset $ inSuper syz . inSuper sxy

-- | The `[]` case of subset proofs.
-- Typlically used with `@@` to build subset proofs out of membership proofs.
nobody :: Subset '[] ys
nobody = Subset \case {}

-- | Any lists is a subset of the list made by consing itself with another item.
consSet :: forall xs x xs'. (xs ~ (x ': xs')) => Subset xs' (x ': xs')
consSet = Subset Later

-- | Cons an element to the superset in a t`Subset` value.
consSuper :: forall xs ys y. Subset xs ys -> Subset xs (y ': ys)
consSuper sxy = transitive sxy consSet

-- | Cons an element to the subset in a t`Subset` value;
--   requires proof that the new head element is already a member of the superset.
--   Used like ":" for subset proofs.
--   Suppose you have @(alice :: Member "Alice" census)@
--   and we want a /subset/ proof instead of membership; we can write:
--
--   >>> proof :: Subset '["Alice"] census = alice @@ nobody
(@@) :: Member x ys -> Subset xs ys -> Subset (x ': xs) ys
infixr 5 @@
mxy @@ sxy = Subset \case
  First -> mxy
  Later mxxs -> inSuper sxy mxxs


-- * Explicit Membership
--
-- $explicit
--
-- When all the concret types/symbols etc are availible to GHC for inxpection, there's no need to write your own proofs.
-- This naieve system stops working as soon as you introduce polymorphism.

-- | Quickly build membership proofs, when the membership can be directly observed by GHC.
class ExplicitMember (x :: k) (xs :: [k]) where
  explicitMember :: Member x xs

instance {-# OVERLAPPABLE #-} (ExplicitMember x xs) => ExplicitMember x (y ': xs) where
  explicitMember = inSuper consSet explicitMember

instance {-# OVERLAPS #-} ExplicitMember x (x ': xs) where
  explicitMember = First

-- | Quickly build subset proofs, when the subset relation can be directly observed by GHC.
class ExplicitSubset xs ys where
  explicitSubset :: Subset xs ys

instance {-# OVERLAPPABLE #-} (ExplicitSubset xs ys, ExplicitMember x ys) => ExplicitSubset (x ': xs) ys where
  explicitSubset = explicitMember @@ explicitSubset

instance {-# OVERLAPS #-} ExplicitSubset '[] ys where
  explicitSubset = nobody

