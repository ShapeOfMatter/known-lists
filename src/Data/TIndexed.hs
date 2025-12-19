-- | Types, functions, and structures for writing choreographies with variable numbers of participants.
module Data.TIndexed where

import Data.Foldable (toList)
import Data.Functor.Compose (Compose (getCompose))
import Data.Functor.Const (Const (Const, getConst))
import Data.Membership
import Data.Proxy (Proxy (..))
import Data.Known
import qualified Data.Typeable as Tpbl
import qualified GHC.Exts as EXTS

-- * The root abstraction

-- | A mapping, accessed by `Member` terms, from types to values.
--   The types of the values depend on the indexing type; this relation is expressed by the type-level function @f@.
--   If the types of the values /don't/ depend on the index, use t`Quire`.
--   If the types vary only in that they are `Located` at the indexing party, use `Faceted`.
--   t`PIndexed` generalizes those two types in a way that's not usually necessary when writing choreographies.
newtype PIndexed ls f = PIndexed {pindex :: PIndex ls f}

-- | An impredicative quantified type. Wrapping it up in t`PIndexed` wherever possible will avoid a lot of type errors and headache.
type PIndex (ls :: [k]) f = forall (l :: k). (Known k l) => Member l ls -> f l

-- | Sequence computations indexed by parties.
--   Converts a t`PIndexed` of computations into a computation yielding a t`PIndexed`.
--   Strongly analogous to 'Data.Traversable.sequence'.
--   In most cases, the [choreographic functions](#g:choreographicfunctions) below will be easier to use
--   than messing around with `Data.Functor.Compose.Compose`.
sequenceP ::
  forall {k} b (ls :: [k]) m.
  (Known [k] ls, Monad m) =>
  PIndexed ls (Compose m b) ->
  m (PIndexed ls b)
sequenceP (PIndexed f) = case tySpine @k @ls of
  TyCons _ (_ :: Proxy ts) -> do
    b <- getCompose $ f First
    PIndexed fTail <- sequenceP (PIndexed @ts @(Compose m b) $ f . Later)
    let retVal :: PIndex (ls :: [k]) b
        retVal First = b
        retVal (Later ltr) = fTail ltr
    pure $ PIndexed retVal
  TyNil -> pure $ PIndexed \case {}

-- * A type-indexed vector type

-- | A collection of values, all of the same type, assigned to each element of the type-level list.
newtype Quire parties a = Quire {asPIndexed :: PIndexed parties (Const a)}

-- | Access a value in a t`Quire` by its index.
getLeaf :: (Known k p) => Quire parties a -> Member p parties -> a
getLeaf (Quire (PIndexed q)) p = getConst $ q p

-- | Package a function as a t`Quire`.
stackLeaves :: forall {k} ps a. (forall p. (Known k p) => Member p ps -> a) -> Quire ps a
stackLeaves f = Quire . PIndexed $ Const . f

-- | Get the head item from a t`Quire`.
qHead :: (Known k p) => Quire (p ': ps) a -> a
qHead (Quire (PIndexed f)) = getConst $ f First

-- | Get the tail of a t`Quire`.
qTail :: Quire (p ': ps) a -> Quire ps a
qTail (Quire (PIndexed f)) = Quire . PIndexed $ f . Later

-- | Prepend a value to a t`Quire`.
--   The corresponding `Symbol` to bind it to must be provided by type-application if it can't be infered.
qCons :: forall p ps a. a -> Quire ps a -> Quire (p ': ps) a
qCons a (Quire (PIndexed f)) = Quire . PIndexed $ \case
  First -> Const a
  Later mps -> f mps

-- | An empty t`Quire`.
qNil :: Quire '[] a
qNil = Quire $ PIndexed \case {}

-- | Apply a function to a single item in a t`Quire`.
qModify :: forall {k} p ps a. (Known k p, Known [k] ps) => Member p ps -> (a -> a) -> Quire ps a -> Quire ps a
qModify First f q = f (qHead q) `qCons` qTail q
qModify (Later m) f q = case tySpine @k @ps of TyCons _ _ -> qHead q `qCons` qModify m f (qTail q)

instance forall k parties. (Known [k] parties) => Functor (Quire parties) where
  fmap f q = case tySpine @k @parties of
    TyCons _ _ -> f (qHead q) `qCons` fmap f (qTail q)
    TyNil -> qNil

instance forall k parties. (Known [k] parties) => Applicative (Quire parties) where
  pure a = Quire . PIndexed $ const (Const a)
  qf <*> qa = case tySpine @k @parties of
    TyCons _ _ -> qHead qf (qHead qa) `qCons` (qTail qf <*> qTail qa)
    TyNil -> qNil

instance forall k parties. (Known [k] parties) => Foldable (Quire parties) where
  foldMap f q = case tySpine @k @parties of
    TyCons _ _ -> f (qHead q) <> foldMap f (qTail q)
    TyNil -> mempty

instance forall k parties. (Known [k] parties) => Traversable (Quire parties) where
  sequenceA q = case tySpine @k @parties of
    TyCons _ _ -> qCons <$> qHead q <*> sequenceA (qTail q)
    TyNil -> pure qNil

instance forall k parties a. (Known [k] parties, Eq a) => Eq (Quire parties a) where
  q1 == q2 = and $ (==) <$> q1 <*> q2

instance forall k parties a. (Known [k] parties, Show (ValType k), Show a) => Show (Quire parties a) where
  show q = show $ toValue (refl @parties) `zip` toList q

instance forall k parties a. (Known [k] parties, Eq (ValType k)) => EXTS.IsList (Quire parties a) where
  type Item (Quire (parties :: [k]) a) = (ValType k, a)
  toList = zip (toValue $ refl @parties) . toList
  fromList items = case (tySpine @k @parties, items) of
    (TyCons h _, (name, i) : is) | name == toValue h -> qCons i $ EXTS.fromList is
    (TyNil, []) -> qNil
    (TyCons h _, (name, _) : _) -> let name' :: String = show $ Tpbl.typeOf name
                                       n'' :: String = show $ Tpbl.typeRep h
                                   in error $ "Provided value of type " ++ name' ++ " is the wrong key for the next item (" ++ n'' ++ ") in the Quire."
    _ -> error $ "List has wrong number of items (" ++ show (length items) ++ ") for use as a Quire over " ++ show (Tpbl.typeRep $ Proxy @parties) ++ "."

-- Many more instances are possible...

