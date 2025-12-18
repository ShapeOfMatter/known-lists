-- | Term level proofs of membership and subset relations among type-level lists.
module Data.Membership where

import Data.Known
import Data.Proxy (Proxy (..))

-- * Membership proofs

-- | A term-level proof that a type is a member of a list of types.
--   These are frequently used both for proofs /per se/ and to identify individuals in such a list.
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
instance Proxies (Member x ys) x where
  proxy _ = Proxy

-- | Any element @p@ is a member of the list @'[p]@.
alone :: forall p. Member p (p ': '[])
alone = First

-- | Use any membership proof to to safely call code that only works on a non-empy list.
quorum1 ::
  forall {k} (ps :: [k]) (p :: k) a.
  (Known [k] ps) =>
  Member p ps ->
  (forall q qs. (Known k q, Known [k] qs, ps ~ q ': qs) => a) ->
  a
quorum1 p a = case (p, tySpine @k @ps) of
  (First, TyCons _ _) -> a
  (Later _, TyCons _ _) -> a

-- * Easy indexing with `Member` objects.

-- | A `Member` value for the first item in a list.
--   Note that type-applicaiton is different than with `First`, to which this is otherwise redundant.
listedFirst :: forall p1 ps. Member p1 (p1 ': ps) -- Can we replace all of these with something using off-the-shelf type-level Nats?
listedFirst = First

-- | A `Member` value for the second item in a list.
listedSecond :: forall p2 p1 ps. Member p2 (p1 ': p2 ': ps)
listedSecond = inSuper (consSuper refl) listedFirst

-- | A `Member` value for the third item in a list.
listedThird :: forall p3 p2 p1 ps. Member p3 (p1 ': p2 ': p3 ': ps)
listedThird = inSuper (consSuper refl) listedSecond

-- | A `Member` value for the forth item in a list.
listedForth :: forall p4 p3 p2 p1 ps. Member p4 (p1 ': p2 ': p3 ': p4 ': ps)
listedForth = inSuper (consSuper refl) listedThird

-- | A `Member` value for the fifth item in a list.
listedFifth :: forall p5 p4 p3 p2 p1 ps. Member p5 (p1 ': p2 ': p3 ': p4 ': p5 ': ps)
listedFifth = inSuper (consSuper refl) listedForth

-- | A `Member` value for the sixth item in a list.
listedSixth :: forall p6 p5 p4 p3 p2 p1 ps. Member p6 (p1 ': p2 ': p3 ': p4 ': p5 ': p6 ': ps)
listedSixth = inSuper (consSuper refl) listedFifth

-- * Subset proofs
--
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

-- | The subset relation is reflexive.
refl :: Subset xs xs
refl = Subset id

-- | Alias `refl`. When used as an identifier, this is more descriptive.
allOf :: forall ps. Subset ps ps
allOf = refl

-- | The sublist relation is transitive.
transitive :: Subset xs ys -> Subset ys zs -> Subset xs zs
transitive sxy syz = Subset $ inSuper syz . inSuper sxy

-- | The `[]` case of subset proofs.
-- Typlically used to build subset proofs using membership proofs using `@@`.
nobody :: Subset '[] ys
nobody = Subset \case {}

-- | Any lists is a subset of the list made by consing itself with any other item.
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

