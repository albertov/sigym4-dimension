
module Sigym4.Dimension.CronScheduleSpec (main, spec) where
import Test.Hspec
import Sigym4.Dimension
import Sigym4.Dimension.CronSchedule
import System.Cron
import Data.Maybe (fromJust, isJust)

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "BCronField" $ do
    context "ListField" $ do
      context "dsucc" $ do
        it "returns correct result" $ do
            let cf = CF f 1 12
                f  = ListField [SpecificField 4, RangeField 7 10]
                t  = idfloor cf 4
                t1 = idsucc cf (fromJust t)
                t2 = idsucc cf (fromJust t1)
                t3 = idsucc cf (fromJust t2)
                t4 = idsucc cf (fromJust t3)
                t5 = idsucc cf (fromJust t4)
            fmap unQ t  `shouldBe` Just 4 
            fmap unQ t1 `shouldBe` Just 7
            fmap unQ t2 `shouldBe` Just 8
            fmap unQ t3 `shouldBe` Just 9
            fmap unQ t4 `shouldBe` Just 10
            isJust t5 `shouldBe` False

      context "dpred" $ do
        it "returns correct result" $ do
            let cf = CF f 1 12
                f  = ListField [SpecificField 4, RangeField 7 10]
                t  = idceiling cf 10
                t1 = idpred cf (fromJust t)
                t2 = idpred cf (fromJust t1)
                t3 = idpred cf (fromJust t2)
                t4 = idpred cf (fromJust t3)
                t5 = idpred cf (fromJust t4)
            fmap unQ t  `shouldBe` Just 10
            fmap unQ t1 `shouldBe` Just 9
            fmap unQ t2 `shouldBe` Just 8
            fmap unQ t3 `shouldBe` Just 7
            fmap unQ t4 `shouldBe` Just 4
            isJust t5 `shouldBe` False
