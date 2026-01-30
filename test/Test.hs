module Main (main) where

import Data.Known.Knowable
import Data.Known.Membership
import Data.Proxy (Proxy (..))
import Example
import qualified GHC.TypeLits as T

testFailure :: String -> String -> IO a
testFailure name msg = ioError . userError . unlines $ ["Failed test: " ++ name
                                                       ,"  Message: " ++ msg]

data Test a = Test { name :: String, test :: IO (Either String a)}
instance Show (Test a) where show = name
instance Functor Test where fmap f t@Test{test} = t{test = (fmap f) <$> test}
instance Applicative Test where
  pure a = Test ("Pure Value") . pure . pure $ a
  liftA2 f t1 t2 = Test (name t1 ++ "<!>" ++ name t2) do r1 <- test t1
                                                         r2 <- test t2
                                                         pure $ f <$> r1 <*> r2

equality :: (Eq a) => Test (a -> a -> Bool)
equality = Test "Equality" (pure . pure $ (==))
pureShown :: (Show a) => a -> Test a
pureShown a = Test (show a) (pure . pure $ a)

tests :: [Test Bool]
tests = [ tautology
        --, crash        --, report        --, opaque
        , valueOf0
        , valueOfFoo
        , valueOfES
        , valueOfSpace
        , valueOfNil
        , valueOfSingleton
        , valueOfFour
        , valueOfSingleNil
        , valueOfRagged
        , valueOfMember
        , showMember
        , showSubset
        , exampleReadMe1
        , exampleReadMe2
        , exampleReadMe3
        ]

tautology :: Test Bool
tautology = pureShown True

valueOf0 :: Test Bool
valueOf0 = equality <*> pureShown 0 <*> pureShown (toValue (Proxy :: Proxy 0))

valueOfFoo :: Test Bool
valueOfFoo = equality <*> pureShown "Foo" <*> pureShown (toValue (Proxy :: Proxy "Foo"))

valueOfES :: Test Bool
valueOfES = equality <*> pureShown "" <*> pureShown (toValue (Proxy :: Proxy ""))

valueOfSpace :: Test Bool
valueOfSpace = equality <*> pureShown ' ' <*> pureShown (toValue (Proxy :: Proxy ' '))

valueOfNil :: Test Bool
valueOfNil = equality <*> pureShown [] <*> pureShown (toValue (Proxy :: Proxy ('[] :: [T.Symbol])))

valueOfSingleton :: Test Bool
valueOfSingleton = equality <*> pureShown ["FooBar"] <*> pureShown (toValue (Proxy :: Proxy '["FooBar"]))

valueOfFour :: Test Bool
valueOfFour = equality <*> pureShown "Four" <*> pureShown (toValue (Proxy :: Proxy '[ 'F', 'o', 'u', 'r']))

valueOfSingleNil :: Test Bool
valueOfSingleNil = equality <*> pureShown [[]] <*> pureShown (toValue (Proxy :: Proxy '[ '[] :: [T.Symbol]]))

valueOfRagged :: Test Bool
valueOfRagged = equality <*> pureShown [[5, 0], [100]] <*> pureShown (toValue (Proxy :: Proxy '[ '[5, 0], '[100] ]))

valueOfMember :: Test Bool
valueOfMember = equality <*> pureShown 111 <*> pureShown (toValue (alone @111))

showMember :: Test Bool
showMember = equality <*> pureShown "Member \"aa\" [\"bb\",\"aa\"]" <*> fmap show (pureShown (Later First :: Member "aa" '["bb", "aa"]))

showSubset :: Test Bool
showSubset = equality <*> pureShown "Subset [\"aa\"] [\"bb\",\"aa\"]" <*> fmap show (pureShown (listedSecond @@ nobody :: Subset '["aa"] '["bb", "aa"]))

{-
crash :: Test
crash = ("Crash",error "Raise error in stead of providing an IO.")
report :: Test
report = ("Report",pure $ Left "Reporting that this test failed.")
opaque :: Test
opaque = ("Opaque",pure $ pure False)
-}

exampleReadMe1 :: Test Bool
exampleReadMe1 = equality <*> pureShown startList <*> fmap (
        raggedToList . raggedFromList @'[] @Int
        ) (pureShown startList)
    where startList = []

type ThreeThreeTwo = '[ '[ '(), '(), '() ], '[ '(), '(), '() ], '[ '(), '() ] ]

exampleReadMe2 :: Test Bool
exampleReadMe2 = equality <*> pureShown startList <*> fmap (
        raggedToList . raggedFromList @ThreeThreeTwo @Int
        ) (pureShown startList)
    where startList = [1 .. 8]

exampleReadMe3 :: Test Bool
exampleReadMe3 = equality <*> pureShown 5 <*> fmap (
        (!!! (listedSecond, listedSecond)) . raggedFromList @ThreeThreeTwo @Int
        ) (pureShown startList)
    where startList = [1 .. 8]

runTest :: Test Bool -> IO ()
runTest Test{name, test} = do
  result <- test
  x <- either (testFailure name) return result
  if x
    then pure ()
    else testFailure name "Unknown failure"

main :: IO ()
main = do
  putStrLn "STARTING TESTS."
  successes <- traverse runTest tests
  let quantity = length successes
  putStrLn $ "FINISHED " ++ show quantity ++ " TESTS."

