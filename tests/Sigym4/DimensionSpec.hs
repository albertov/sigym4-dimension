{-# LANGUAGE ScopedTypeVariables, TypeOperators, FlexibleContexts #-}
module Sigym4.DimensionSpec (main, spec) where
import Control.Applicative
import Test.Hspec
import Test.Hspec.QuickCheck
import Sigym4.Dimension
import Data.Time.Calendar
import Data.Time.Clock
import Data.List as L
import Data.Maybe (isJust)
import Test.QuickCheck
import System.Cron
import GHC.Exts (fromList)

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "dfloor" $ do

    context "Schedule ObservationTime" $ do

        it "returns an element of dimension" $ property $
            \((d::Schedule ObservationTime), i) ->
                fmap (`delem` d) (dfloor d i) == Just True

        it "is transitive for ordering" $ property $
            \((d::Schedule ObservationTime), (a,b,c)) ->
              let fa'     = dfloor d a
                  fb'     = dfloor d b
                  fc'     = dfloor d c
                  Just fa = fa'
                  Just fb = fb'
                  Just fc = fc'
              in a < b && b < c && isJust fa' && isJust fb' && isJust fc'  ==>
                ((fa `compare` fb) `elem` [EQ, LT])
                  &&
                ((fb `compare` fc) `elem` [EQ, LT])
                  &&
                ((fa `compare` fc) `elem` [EQ, LT])


    context "Horizons :> Schedule RunTime" $ do

        it "returns an element of dimension" $ property $
            \((d :: Horizons :> Schedule RunTime), i) ->
                fmap (`delem` d) (dfloor d i) == Just True

        it "is transitive for ordering" $ property $
            \((d :: Horizons :> Schedule RunTime), (a,b,c)) ->
              let fa'     = dfloor d a
                  fb'     = dfloor d b
                  fc'     = dfloor d c
                  Just fa = fa'
                  Just fb = fb'
                  Just fc = fc'
              in a < b && b < c && isJust fa' && isJust fb' && isJust fc'  ==>
                ((fa `compare` fb) `elem` [EQ, LT])
                  &&
                ((fb `compare` fc) `elem` [EQ, LT])
                  &&
                ((fa `compare` fc) `elem` [EQ, LT])

  describe "dceiling" $ do

    context "Schedule ObservationTime" $ do

        it "returns an element of dimension" $ property $
            \((d::Schedule ObservationTime), i) ->
                fmap (`delem` d) (dceiling d i) == Just True

        it "is transitive for ordering" $ property $
            \((d::Schedule ObservationTime), (a,b,c)) ->
              let fa'     = dceiling d a
                  fb'     = dceiling d b
                  fc'     = dceiling d c
                  Just fa = fa'
                  Just fb = fb'
                  Just fc = fc'
              in a > b && b > c && isJust fa' && isJust fb' && isJust fc'  ==>
                ((fa `compare` fb) `elem` [EQ, GT])
                  &&
                ((fb `compare` fc) `elem` [EQ, GT])
                  &&
                ((fa `compare` fc) `elem` [EQ, GT])


    context "Horizons :> Schedule RunTime" $ do

        it "returns an element of dimension" $ property $
            \((d :: Horizons :> Schedule RunTime), i) ->
                fmap (`delem` d) (dceiling d i) == Just True

        it "is transitive for ordering" $ property $
            \((d :: Horizons :> Schedule RunTime), (a,b,c)) ->
              let fa'     = dceiling d a
                  fb'     = dceiling d b
                  fc'     = dceiling d c
                  Just fa = fa'
                  Just fb = fb'
                  Just fc = fc'
              in a > b && b > c && isJust fa' && isJust fb' && isJust fc'  ==>
                ((fa `compare` fb) `elem` [EQ, GT])
                  &&
                ((fb `compare` fc) `elem` [EQ, GT])
                  &&
                ((fa `compare` fc) `elem` [EQ, GT])


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

nonNeg :: Gen (NonNegative Int)
nonNeg = arbitrary

instance Arbitrary UTCTime where
    arbitrary
      = UTCTime <$> (ModifiedJulianDay . fromIntegral <$> nonNeg)
                <*> (fromIntegral <$> (choose (0, 24*3600-1) :: Gen Int))

instance (Arbitrary a, Arbitrary b) => Arbitrary (a :> b) where
    arbitrary = (:>) <$> arbitrary <*> arbitrary

instance Arbitrary Horizons where
    arbitrary = fromList <$> listOf1 arbitrary

instance Arbitrary Horizon where
    arbitrary = Minute . fromIntegral <$> nonNeg

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
        if lo<hi
        then return $ RangeField lo hi
        else rangeField
    listField     = ListField  <$>
                       listOf1 (oneof [star,specificField,rangeField
                                      ,stepField])
    stepField     = StepField  <$> star <*> choose ( max 1 (fst range)
                                                   , snd range)
