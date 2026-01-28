-- | Types, functions, and structures for writing choreographies with variable numbers of participants.
module Data.Known.TypeIndexed where

import Data.Bifunctor.Flip
import Data.Kind (Type)
import Data.Foldable (toList)
import Data.Functor.Compose (Compose (Compose, getCompose))
import Data.Functor.Const (Const (Const, getConst))
import Data.Proxy (Proxy (..))
import Data.Known.Knowable
import Data.Known.Membership
import qualified Data.Typeable as Tpbl
import qualified GHC.Exts as EXTS

-- * The root abstraction

-- | A mapping, accessed by `Member` terms, from types to values.
--   The types of the values depend on the indexing type; this relation is expressed by the type-level function @f@.
--   If the types of the values /don't/ depend on the index, use t`TVec`.
--   If the types vary only in that they are `Located` at the indexing party, use `Faceted`.
--   t`TIndexed` generalizes those two types in a way that's not usually necessary when writing choreographies.
newtype TIndexed ts f = TIndexed {tindex :: TIndex ts f}

-- | An impredicative quantified type. Wrapping it up in t`TIndexed` wherever possible will avoid a lot of type errors and headache.
type TIndex (ts :: [k]) (f :: k -> Type) = forall (t :: k). (Known k t) => Member t ts -> f t

instance (Known [k] ts, forall t. Functor (m t)) => Functor (Compose (TIndexed ts) (Flip m)) where
  fmap = cpmap . flipmap
    where cpmap :: (forall t. Flip m a t -> Flip m b t) -> Compose (TIndexed ts) (Flip m) a -> Compose (TIndexed ts) (Flip m) b
          cpmap f (Compose (TIndexed i)) = Compose . TIndexed $ f . i
          flipmap :: (forall t. Functor (m t)) => (a -> b) -> (forall t. Flip m a t -> Flip m b t)
          flipmap f = Flip . fmap f . runFlip

instance (Known [k] ts, forall t. Foldable (m t)) => Foldable (Compose (TIndexed ts) (Flip m)) where
  foldMap (f :: a -> monoid) (Compose (TIndexed m)) = fmGo (refl @ts)
    where fm :: TIndex ts (Const monoid)
          fm t = Const . foldMap f . runFlip $ m t
          fmGo :: forall ts'. (Known [k] ts') => Subset ts' ts -> monoid
          fmGo ts' = case tySpine @k @ts' of
            TyNil -> mempty
            TyCons _ _ -> getConst (fm $ inSuper ts' listedFirst) <> fmGo (consSet @ts' `transitive` ts')


-- FIX: can't do a traversablee this way.
-- The inner applicative isn't necessarily the _same_ effect for each party, so they can't meaningfully be sequenced.
-- Gotta recapitulate the compose bs from sequenceP.
{-instance (Known [k] ls, Monad m) => Traversable (Compose (TIndexed ls) (Compose (Flip m))) where
  --sequenceA (c :: Compose (TIndexed ls) (Flip m) a) = case tySpine @k @ls of
  sequenceA c = case tySpine @k @ls of
      TyCons _ (_ :: Proxy (ts :: [k])) -> do
        let m = tindex . getCompose $ c
        b <- runFlip $ m First
        --TIndexed fTail <- sequenceA (TIndexed @ts @(Flip m a) $ m . Later)
        TIndexed fTail <- sequenceA (TIndexed @ts  $ m . Later)
        let retVal :: TIndex (ls :: [k]) b
            retVal First = b
            retVal (Later ltr) = fTail ltr
        pure $ TIndexed retVal
      TyNil -> pure . Compose $ TIndexed \case {}-}

{- Punt on all this until I'm sure the applicative instance is lawful...
_cplift :: (forall l. Flip m a l -> Flip m b l -> Flip m c l ...
_fliplift :: (forall l. Applicative (m l)) => (a -> b -> c) -> (forall l. Flip m a l -> Flip m b l -> Flip m c l)
_fliplift f a b = Flip $ (liftA2 f) (runFlip a) (runFlip b)
instance (Known [k] ls, forall l. Applicative (m l)) => Applicative (Compose (TIndexed ls) (Flip m)) where
  pure a = Compose . TIndexed $ const . Flip . pure $ a
  liftA2 f (Compose (TIndexed a)) (Compose (TIndexed b)) = Compose . TIndexed $ \l -> _fliplift f (a l) (b l)
instance (Known [k] ls, forall l. Monad (m l)) => Monad (Compose (TIndexed ls) (Flip m)) where
-}
    

-- | Sequence computations indexed by parties.
--   Converts a t`TIndexed` of computations into a computation yielding a t`TIndexed`.
--   Strongly analogous to 'Data.Traversable.sequence'.
--   In most cases, the [choreographic functions](#g:choreographicfunctions) below will be easier to use
--   than messing around with `Data.Functor.Compose.Compose`.
sequenceP ::
  forall {k} (b :: k -> Type) (ts :: [k]) (m :: Type -> Type) .
  (Known [k] ts, Applicative m) =>
  TIndexed ts (Compose m b) ->
  m (TIndexed ts b)
sequenceP (TIndexed f) = case tySpine @k @ts of
  TyCons (_ :: Proxy head) (_ :: Proxy (tail :: [k])) ->
    let b = getCompose $ f First
        fTail = tindex <$> sequenceP (TIndexed $ f . Later)
        retIndex :: b head -> TIndex tail b -> TIndex ts b
        retIndex b' _ First = b'
        retIndex _ ts' (Later ltr) = ts' ltr
        rv = retIndex <$> b <*> fTail
    in TIndexed <$> rv
  TyNil -> pure $ TIndexed \case {}

-- * A type-indexed vector type

-- | A collection of values, all of the same type, assigned to each element of the type-level list.
newtype TVec ts a = TVec {asTIndexed :: TIndexed ts (Const a)}

-- | Access a value in a t`TVec` by its index.
(!) :: (Known k t) => TVec ts a -> Member t ts -> a
(!) (TVec (TIndexed f)) t = getConst $ f t

-- | Package a function as a t`TVec`.
pack :: forall {k} ts a. (forall t. (Known k t) => Member t ts -> a) -> TVec ts a
pack f = TVec . TIndexed $ Const . f

-- | Get the head item from a t`TVec`.
tHead :: (Known k t) => TVec (t ': ts) a -> a
tHead (TVec (TIndexed f)) = getConst $ f First

-- | Get the tail of a t`TVec`.
tTail :: TVec (p ': ps) a -> TVec ps a
tTail (TVec (TIndexed f)) = TVec . TIndexed $ f . Later

-- | Prepend a value to a t`TVec`.
--   The corresponding `Symbol` to bind it to must be provided by type-application if it can't be infered.
tCons :: forall p ps a. a -> TVec ps a -> TVec (p ': ps) a
tCons a (TVec (TIndexed f)) = TVec . TIndexed $ \case
  First -> Const a
  Later mps -> f mps

-- | An empty t`TVec`.
tNil :: TVec '[] a
tNil = TVec $ TIndexed \case {}

-- | Apply a function to a single item in a t`TVec`.
tModify :: forall {k} p ps a. (Known k p, Known [k] ps) => Member p ps -> (a -> a) -> TVec ps a -> TVec ps a
tModify First f q = f (tHead q) `tCons` tTail q
tModify (Later m) f q = case tySpine @k @ps of TyCons _ _ -> tHead q `tCons` tModify m f (tTail q)

instance forall k ts. (Known [k] ts) => Functor (TVec ts) where
  fmap f v = case tySpine @k @ts of
    TyCons _ _ -> f (tHead v) `tCons` fmap f (tTail v)
    TyNil -> tNil

instance forall k ts. (Known [k] ts) => Applicative (TVec ts) where
  pure a = TVec . TIndexed $ const (Const a)
  vf <*> va = case tySpine @k @ts of
    TyCons _ _ -> tHead vf (tHead va) `tCons` (tTail vf <*> tTail va)
    TyNil -> tNil

instance forall k ts. (Known [k] ts) => Foldable (TVec ts) where
  foldMap f v = case tySpine @k @ts of
    TyCons _ _ -> f (tHead v) <> foldMap f (tTail v)
    TyNil -> mempty

instance forall k ts. (Known [k] ts) => Traversable (TVec ts) where
  sequenceA v = case tySpine @k @ts of
    TyCons _ _ -> tCons <$> tHead v <*> sequenceA (tTail v)
    TyNil -> pure tNil

instance forall k ts a. (Known [k] ts, Eq a) => Eq (TVec ts a) where
  v1 == v2 = and $ (==) <$> v1 <*> v2

instance forall k ts a. (Known [k] ts, Show (ValType k), Show a) => Show (TVec ts a) where
  show v = show $ toValue (refl @ts) `zip` toList v

instance forall k ts a. (Known [k] ts, Eq (ValType k)) => EXTS.IsList (TVec ts a) where
  type Item (TVec (ts :: [k]) a) = (ValType k, a)
  toList = zip (toValue $ refl @ts) . toList
  fromList items = case (tySpine @k @ts, items) of
    (TyCons h _, (name, i) : is) | name == toValue h -> tCons i $ EXTS.fromList is
    (TyNil, []) -> tNil
    (TyCons h _, (name, _) : _) -> let name' = show $ Tpbl.typeOf name
                                       n'' = show $ Tpbl.typeRep h
                                   in error $ "Provided value of type " ++ name' ++ " is the wrong key for the next item (" ++ n'' ++ ") in the TVec."
    _ -> error $ "List has wrong number of items (" ++ show (length items) ++ ") for use as a TVec over " ++ show (Tpbl.typeRep $ Proxy @ts) ++ "."

-- Many more instances are possible...

