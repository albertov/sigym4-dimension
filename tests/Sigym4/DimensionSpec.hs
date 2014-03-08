{-# LANGUAGE ScopedTypeVariables, TypeOperators #-}
module Sigym4.DimensionSpec (main, spec) where
import Control.Applicative
import Test.Hspec
import Test.Hspec.QuickCheck
import Sigym4.Dimension
import Data.Time.Calendar
import Data.Time.Clock
import Data.List as L
import Test.QuickCheck
import System.Cron
import GHC.Exts (fromList)

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "denumUp" $ do

    context "Schedule ObservationTime" $ do

        it "returns only elements of dimension" $ property $
            \((d::Schedule ObservationTime), i) ->
                all (`delem` d) $ take 10 $ denumUp d i

        it "returns sorted elements" $ property $
            \((d::Schedule ObservationTime), i) ->
                let elems = take 10 $ denumUp d i
                in L.sort elems == elems

    context "Horizons :> Schedule RunTime" $ do

        it "returns only elements of product dimension" $ property $
            \((d :: Horizons :> Schedule ObservationTime), i) ->
                all (`delem` d) $ take 10 $ denumUp d i

        it "returns sorted elements" $ property $
            \((d :: Horizons :> Schedule RunTime), i) ->
                let elems = take 10 $ denumUp d i
                in L.sort elems == elems

  describe "denumDown" $ do

    context "Schedule ObservationTime" $ do

        it "returns only elements of dimension" $ property $
            \((d::Schedule ObservationTime), i) ->
                all (`delem` d) $ take 10 $ denumDown d i

        it "returns reversely sorted elements" $ property $
            \((d::Schedule ObservationTime), i) ->
                let elems = take 10 $ denumDown d i
                in L.sort elems == reverse elems

    context "Horizons :> Schedule RunTime" $ do

        it "returns only elements of product dimension" $ property $
            \((d :: Horizons :> Schedule ObservationTime), i) ->
                all (`delem` d) $ take 10 $ denumDown d i

        it "returns reversely sorted elements" $ property $
            \((d :: Horizons :> Schedule RunTime), i) ->
                let elems = take 10 $ denumDown d i
                in L.sort elems == reverse elems


-- A continuación se implementan instancias de Arbitrary de varios tipos
-- para poder generar valores aleatorios para tests de propiedades
instance Arbitrary ForecastTime where
    arbitrary = fromUTCTime <$> arbitrary

instance Arbitrary RunTime where
    arbitrary = fromUTCTime <$> arbitrary

instance Arbitrary ObservationTime where
    arbitrary = fromUTCTime <$> arbitrary

instance Arbitrary UTCTime where
    arbitrary
      = UTCTime <$> (ModifiedJulianDay <$> arbitrary)
                <*> (fromIntegral      <$> (arbitrary :: Gen (NonNegative Int)))

instance (Arbitrary a, Arbitrary b) => Arbitrary (a :> b) where
    arbitrary = (:>) <$> arbitrary <*> arbitrary

instance Arbitrary Horizons where
    arbitrary = fromList <$> listOf1 arbitrary

instance Arbitrary Horizon where
    arbitrary = Minute <$> arbitrary

instance Arbitrary (Schedule t) where
    arbitrary = Schedule <$> arbitrary

instance Arbitrary CronSchedule where
    arbitrary = CronSchedule <$> arbitrary
                             <*> arbitrary
                             -- Los siguientes deberían ser arbitrary pero
                             -- es MUY lento. Hay que optimizar
                             -- denumUp/denumDown para que sean más listos
                             -- generando
                             <*> pure (DaysOfMonth Star)
                             <*> pure (Months Star)
                             <*> pure (DaysOfWeek Star)

instance Arbitrary DayOfWeekSpec where
    arbitrary = DaysOfWeek <$> arbitraryCronField (0,7)
instance Arbitrary DayOfMonthSpec where
    arbitrary = DaysOfMonth <$> arbitraryCronField (1,31)
instance Arbitrary MonthSpec where
    arbitrary = Months <$> arbitraryCronField (1,12)
instance Arbitrary MinuteSpec where
    arbitrary = Minutes <$> arbitraryCronField (0,59)
instance Arbitrary HourSpec where
    arbitrary = Hours <$> arbitraryCronField (0,23)

arbitraryCronField :: (Int,Int) -> Gen CronField
arbitraryCronField range
  = oneof [star,specificField,rangeField,listField,stepField]
  where
    specificField = SpecificField <$> choose range
    star          = pure Star
    rangeField    = do
        lo <- choose range
        hi <- choose range
        if lo<hi then return $ RangeField lo hi
        else rangeField
    listField     = ListField  <$>
                       listOf1 (oneof [star,specificField,rangeField
                                      ,stepField])
    stepField     = StepField  <$> star <*> choose ( max 1 (fst range)
                                                   , snd range)
