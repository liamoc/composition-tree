import Test.DocTest

main :: IO ()
main = doctest ["Data/Compositions/Internal.hs", "Data/Compositions/Snoc.hs"]
