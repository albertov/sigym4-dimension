{-# OPTIONS_GHC -fno-warn-orphans #-}
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

takeSample :: [a] -> [a]
takeSample = take 500

spec :: Spec
spec = do
  describe "delem" $ do
    context "CronSchedule" $
        it "behaves like model" $ property $
            \(s, t) -> t `delem` s == s `scheduleMatches` t

  describe "dsucc" $ do

    context "Schedule ObservationTime" $ do

        it "returns an element belonging to set" $ property $
            \((d::Schedule ObservationTime), i) ->
                fmap (`delem` d) (dsucc d i) == Just True

        it "returns an element strictly greater" $ property $
            \((d::Schedule ObservationTime), i) ->
                fmap (`compare` i) (dsucc d i) == Just GT

    context "Horizons :> Schedule RunTime" $ do

        it "returns an element belonging to set" $ property $
            \((d :: Horizons :> Schedule RunTime), i) ->
                fmap (`delem` d) (dsucc d i) == Just True

        it "returns an element strictly greater" $ property $
            \((d :: Horizons :> Schedule RunTime), i) ->
                fmap (`compare` i) (dsucc d i) == Just GT

  describe "dpred" $ do

    context "Schedule ObservationTime" $ do

        it "returns an element belonging to set" $ property $
            \((d::Schedule ObservationTime), i) ->
                fmap (`delem` d) (dpred d i) == Just True

        it "returns an element strictly smaller" $ property $
            \((d::Schedule ObservationTime), i) ->
                fmap (`compare` i) (dpred d i) == Just LT

    context "Horizons :> Schedule RunTime" $ do

        it "returns an element belonging to set" $ property $
            \((d :: Horizons :> Schedule RunTime), i) ->
                fmap (`delem` d) (dpred d i) == Just True

        it "returns an element strictly smaller" $ property $
            \((d :: Horizons :> Schedule RunTime), i) ->
                fmap (`compare` i) (dpred d i) == Just LT


  describe "dfloor" $ do

    context "Schedule ObservationTime" $ do

        it "returns an element belonging to set" $ property $
            \((d::Schedule ObservationTime), i) ->
                fmap (`delem` d) (dfloor d i) == Just True

        it "returns an element smaller or EQ" $ property $
            \((d::Schedule ObservationTime), i) ->
                fmap ((`elem` [LT,EQ]) . (`compare` i)) (dfloor d i)
                  == Just True

        it "application preserves ordering" $ property $
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

        it "returns an element belonging to set" $ property $
            \((d :: Horizons :> Schedule RunTime), i) ->
                fmap (`delem` d) (dfloor d i) == Just True

        it "returns an element smaller or EQ" $ property $
            \((d :: Horizons :> Schedule RunTime), i) ->
                fmap ((`elem` [LT,EQ]) . (`compare` i)) (dfloor d i)
                  == Just True

        it "application preserves ordering" $ property $
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

        it "returns an element belonging to set" $ property $
            \((d::Schedule ObservationTime), i) ->
                fmap (`delem` d) (dceiling d i) == Just True

        it "returns an element greater or EQ" $ property $
            \((d::Schedule ObservationTime), i) ->
                fmap ((`elem` [GT,EQ]) . (`compare` i)) (dceiling d i)
                  == Just True

        it "application preserves ordering" $ property $
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

        it "returns an element belonging to set" $ property $
            \((d :: Horizons :> Schedule RunTime), i) ->
                fmap (`delem` d) (dceiling d i) == Just True

        it "returns an element greater or EQ" $ property $
            \((d :: Horizons :> Schedule RunTime), i) ->
                fmap ((`elem` [GT,EQ]) . (`compare` i)) (dceiling d i)
                  == Just True

        it "application preserves ordering" $ property $
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
                all (`delem` d) $ takeSample $ denumUp d i

        it "returns sorted elements" $ property $
            \((d::Schedule ObservationTime), i) ->
                let elems = takeSample $ denumUp d i
                in L.sort elems == elems

        it "does not return duplicate elements" $ property $
            \((d::Schedule ObservationTime), i) ->
                let elems = takeSample $ denumUp d i
                in L.nub elems == elems

    context "Horizons :> Schedule RunTime" $ do

        it "returns only elements of product dimension" $ property $
            \((d :: Horizons :> Schedule RunTime), i) ->
                all (`delem` d) $ takeSample $ denumUp d i

        it "returns sorted elements" $ property $
            \((d :: Horizons :> Schedule RunTime), i) ->
                let elems = takeSample $ denumUp d i
                in L.sort elems == elems

        it "does not return duplicate elements" $ property $
            \((d :: Horizons :> Schedule RunTime), i) ->
                let elems = takeSample $ denumUp d i
                in L.nub elems == elems

  describe "denumDown" $ do

    context "Schedule ObservationTime" $ do

        it "returns only elements of dimension" $ property $
            \((d::Schedule ObservationTime), i) ->
                all (`delem` d) $ takeSample $ denumDown d i

        it "returns reversely sorted elements" $ property $
            \((d::Schedule ObservationTime), i) ->
                let elems = takeSample $ denumDown d i
                in L.sort elems == reverse elems

        it "does not return duplicate elements" $ property $
            \((d::Schedule ObservationTime), i) ->
                let elems = takeSample $ denumUp d i
                in L.nub elems == elems

    context "Horizons :> Schedule RunTime" $ do

        it "returns only elements of product dimension" $ property $
            \((d :: Horizons :> Schedule RunTime), i) ->
                all (`delem` d) $ takeSample $ denumDown d i

        it "returns reversely sorted elements" $ property $
            \((d :: Horizons :> Schedule RunTime), i) ->
                let elems = takeSample $ denumDown d i
                in L.sort elems == reverse elems

        it "does not return duplicate elements" $ property $
            \((d :: Horizons :> Schedule RunTime), i) ->
                let elems = takeSample $ denumUp d i
                in L.nub elems == elems


-- A continuación se implementan instancias de Arbitrary de varios tipos
-- para poder generar valores aleatorios para tests de propiedades
instance Arbitrary ForecastTime where
    arbitrary = fromUTCTime <$> arbitrary

instance Arbitrary RunTime where
    arbitrary = fromUTCTime <$> arbitrary

instance Arbitrary ObservationTime where
    arbitrary = fromUTCTime <$> arbitrary

day0, day1 :: Integer
ModifiedJulianDay day0 = fromGregorian 1800 1 1
ModifiedJulianDay day1 = fromGregorian 3000 1 1

instance Arbitrary UTCTime where
    arbitrary
      = UTCTime <$> (ModifiedJulianDay . fromIntegral <$> choose (day0,day1))
                <*> (fromIntegral <$> (choose (0, 24*3600-1) :: Gen Int))

instance (Arbitrary a, Arbitrary b) => Arbitrary (a :> b) where
    arbitrary = (:>) <$> arbitrary <*> arbitrary

instance Arbitrary Horizons where
    arbitrary = fromList <$> listOf1 arbitrary

instance Arbitrary Horizon where
    arbitrary = oneof [ Minute <$> choose (-10000,10000)
                      , Hour   <$> choose (-1000,1000)
                      , Day    <$> choose (-100,100)]

instance Arbitrary (Schedule t) where
    arbitrary = Schedule <$> arbitrary

instance Arbitrary CronSchedule where
    arbitrary = CronSchedule <$> arbitrary
                             <*> arbitrary
                             <*> arbitrary
                             <*> arbitrary
                             <*> pure (DaysOfWeek Star) --TODO

instance Arbitrary DayOfWeekSpec where
    arbitrary = DaysOfWeek <$> arbitraryCronField (0,7)
instance Arbitrary DayOfMonthSpec where
    arbitrary = DaysOfMonth <$> arbitraryCronField (1,28) -- FIXME: poner 31
instance Arbitrary MonthSpec where
    arbitrary = Months <$> arbitraryCronField (1,12)
instance Arbitrary MinuteSpec where
    arbitrary = Minutes <$> arbitraryCronField (0,59)
instance Arbitrary HourSpec where
    arbitrary = Hours <$> arbitraryCronField (0,23)

arbitraryCronField :: (Int,Int) -> Gen CronField
arbitraryCronField range
  = oneof [star,specificField,stepField,rangeField,listField]
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
    stepField     = StepField  <$> oneof [star] --,rangeField]
                               <*> choose ( max 1 (fst range)
                                          , snd range)
