# Known Lists

This library is intended to make basic operations with type-level lists easy.
In particular, it's for situations in which membership of a type-level symbol
(often, but not necessarily, a `Symbol`)
in a list is a critical property to enforce. 

`Data.Known.Knowable` generalises the idea of a "known" type-level symbol;
a `Known` constraint can be used on `Symbol`s, `Nat`s, _etc_,
and on lists of such `Known` types.  
`Data.Known.Membership` contains the key structures and logic for enforcing
membership constraints;
the naive class-based solution (which is also included)
fails in polymorphic code;
this system allows more robust and explicit handling.  
`Data.Known.TypeIndexed` introduces `TIndexed`,
heterogeneous lists indexed by type-level symbols.

This library is an adaptation for general use of an _ad hoc_ system originally used in
[MultiChor](https://hackage.haskell.org/package/MultiChor).
Very likely everything in this library can, should, and eventually will be replaced by some correct
combination of [singletons](https://hackage.haskell.org/package/singletons),
[spo](https://hackage.haskell.org/package/sop-core),
and related libraries,
but until there's good documentation showing new users how to do that, this library will be useful.

## Examples

The entire
[MultiChor](https://hackage.haskell.org/package/MultiChor)
library can be viewed as an example use-case.
Here we show a less involved example which relies on the (morally incidental) fact that `Member` objects
are effectively finite Nats.

To begin with, consider the traditional Haskell fixed-length (length-indexed) vector:

```haskell
data VecN (n :: GHC.TypeLits.Nat) a where
  NNil  :: VecN 0 a
  NCons :: a -> VecN n a -> VecN (n + 1) a

indexN :: VecN n a -> Int -> a  -- UNSAFE: Partial!
indexN (NCons x _) 0          = x
indexN (NCons _ xs) i | 0 < i = indexN xs (i - 1)
indexN _ _                    = error "indexN: Out of bounds."
```

Using a partial function for indexing isn't satisfying.
We can improve on this situation by using lists of Unit and corresponding `Member` values
as Nats and Finite Nats:

```haskell
type Nat = [()]

data VecU (n :: Nat) a where
  UNil  :: VecU '[] a
  UCons :: a -> VecU n a -> VecU ('() ': n) a

indexU :: VecU n a -> Member '() n -> a
indexU (UCons x _) First = x
indexU (UCons _ xs) (Later i) = indexU xs i
indexU UNil i = case i of {}  -- This index function is safe; GHC knows there is no such `i`.
```

But there's no need to actually write out this simple example like that; `known-lists` gives such a type out-of-the-box:

```haskell
type Vec (n :: Nat) a = TVec n a
```

We can extend this example to ragged matrices or arrays.
Note that `RaggedMatrix` can't be expressed using just `TVec`;
the rows have different lengths and the length is encoded in the type, so each row actually has a distinct type.

```haskell
newtype RaggedMatrix (rows :: [Nat]) a = Ragged {
    raggedIndexes :: TIndexed rows (Flip TVec a)
  }

(!!!) :: (Known Nat row)
      => RaggedMatrix rows a
      -> (Member row rows, Member '() row)
      -> a
(!!!) (Ragged TIndexed{tindex}) (row, i) = runFlip (tindex row) ! i
```

Flattening a `RaggedMatrix` into a list is short and sweet.
Populating a `RaggedMatrix` from a flat list demonstrates the use of `tySpine`.

```haskell
raggedToList :: forall rows a. (Known [Nat] rows)
             => RaggedMatrix rows a -> [a]
raggedToList (Ragged (TIndexed f)) = concat lists
  where lists :: TVec rows [a]
        lists = pack (toList . runFlip . f)

raggedFromList :: forall rows a. (Known [Nat] rows)
               => [a] -> RaggedMatrix rows a
raggedFromList xs = case tySpine @Nat @rows of
  TyNil -> Ragged $ TIndexed \case{}
  TyCons (_ :: Proxy r1) (_ :: Proxy rows') ->
                let (xs1, xsTail) = splitAt (knownLength $ allOf @r1) xs
                    -- This is where it will crash if the list isn't big enough:
                    r1 :: TVec r1 a
                    r1 = EXTS.fromList $ zip (repeat ()) xs1
                    f :: TIndex rows' (Flip TVec a)
                    Ragged TIndexed{tindex=f} = raggedFromList xsTail
                in Ragged $ TIndexed \case
                    First -> Flip r1
                    Later i -> f i
```

`sequenceT` allows us to sequence uniform monadic effects over heterogeneous `TIndexed` structures.
In this example, instead of building the `RaggedMatrix` from a list, we read the elements from `stdIn` one at a time.
Since the exact type of the `IO` action needed for each `row` is different, we use `sequenceT`.

```haskell
raggedFromStdIn :: forall rows a. (Read a, Known [Nat] rows)
                => IO (RaggedMatrix rows a)
raggedFromStdIn = Ragged <$> rfsi
  where rfsi :: IO (TIndexed rows (Flip TVec a))
        rfsi = sequenceT $ TIndexed $ Compose <$> rows
        rows :: forall row. (Known Nat row)
             => Member row rows -> IO (Flip TVec a row)
        rows _ = Flip <$> row
        row :: forall row. (Known Nat row) => IO (TVec row a)
        row = fmap TVec $ sequenceT $ TIndexed $
                  Compose . fmap Const <$> item
        item :: forall i row. Member i row -> IO a
        item = const readLn
```

