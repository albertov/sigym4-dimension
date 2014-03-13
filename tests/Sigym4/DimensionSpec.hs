{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings
           , ScopedTypeVariables
           , TypeOperators
           , TypeFamilies
           , FlexibleContexts
           #-}
module Sigym4.DimensionSpec (main, spec) where
import Control.Applicative
import Test.Hspec
import Test.Hspec.QuickCheck
import Data.Time.Calendar
import Data.Time.Clock
import Data.List as L
import Data.Maybe (isJust)
import Data.Either (isRight)
import Data.String (fromString)
import Data.Attoparsec.Text (parseOnly)
import Test.QuickCheck
import System.Cron
import GHC.Exts (fromList)
import System.Cron.Parser (cronSchedule)

import Sigym4.Dimension
import Sigym4.Dimension.Time (Schedule(Schedule))

main :: IO ()
main = hspec spec

takeSample :: [a] -> [a]
takeSample = take 500

spec :: Spec
spec = do

  dimensionSpec "Schedule ObservationTime"
                (Proxy :: Proxy (Schedule ObservationTime))

  dimensionSpec "Horizons :* Schedule RunTime"
                (Proxy :: Proxy (Horizons :* Schedule RunTime))


  context "CronSchedule" $ do
    describe "idelem" $ do
      it "behaves like model" $ property $
        \(s, t) -> s `idelem` t == s `scheduleMatches` t

    describe "leap years" $ do

      describe "idsucc" $ do
        it "returns day 29" $ do
          let sched  = "0 0 * * *" :: CronSchedule
              Just t = idfloor sched (datetime 2012 2 28 0 0)
              Just s = idsucc sched t
          unQ s `shouldBe` datetime 2012 2 29 0 0
        it "accepts day 29" $ do
          let sched  = "0 0 * * *" :: CronSchedule
              Just t = idfloor sched (datetime 2012 2 29 0 0)
              Just s = idsucc sched t
          unQ s `shouldBe` datetime 2012 3 1 0 0

      describe "idpred" $ do
        it "returns day 29" $ do
          let sched  = "0 0 * * *" :: CronSchedule
              Just t = idfloor sched (datetime 2012 3 1 0 0)
              Just s = idpred sched t
          unQ s `shouldBe` datetime 2012 2 29 0 0
        it "accepts day 29" $ do
          let sched  = "0 0 * * *" :: CronSchedule
              Just t = idfloor sched (datetime 2012 2 29 0 0)
              Just s = idpred sched t
          unQ s `shouldBe` datetime 2012 2 28 0 0
             

-- | Una especificación que comprueba que se cumplen las propiedades de
--   'Dimension' en cualquier instancia.
dimensionSpec :: forall dim.
  ( Arbitrary dim, Arbitrary (DimensionIx dim), Dimension dim
  , Dependent dim ~ ())
  => String -> Proxy dim -> Spec
dimensionSpec typeName _ = context ("Dimension ("++typeName++")") $ do
  describe "idsucc" $ do
    it "returns an element strictly greater" $ property $
        \((d::dim), i) ->
        let norm   = idfloor d i
            Just v = norm
        in isJust norm ==> fmap (`compare` v) (idsucc d v) == Just GT

  describe "idpred" $ do
    it "returns an element strictly smaller" $ property $
        \((d::dim), i) ->
        let norm   = idfloor d i
            Just v = norm
        in isJust norm ==> fmap (`compare` v) (idpred d v) == Just LT

  describe "idfloor" $ do
    it "returns an element belonging to set" $ property $
        \((d::dim), i) ->
            fmap ((idelem d) . unQ) (idfloor d i) == Just True

    it "returns an element smaller or EQ" $ property $
        \((d::dim), i) ->
            fmap ((`elem` [LT,EQ]) . (`compare` i) . unQ) (idfloor d i)
              == Just True

    it "application preserves ordering" $ property $
        \((d::dim), (a,b,c)) ->
          let fa'     = idfloor d a
              fb'     = idfloor d b
              fc'     = idfloor d c
              Just fa = fa'
              Just fb = fb'
              Just fc = fc'
          in a < b && b < c && isJust fa' && isJust fb' && isJust fc'  ==>
            ((fa `compare` fb) `elem` [EQ, LT])
              &&
            ((fb `compare` fc) `elem` [EQ, LT])
              &&
            ((fa `compare` fc) `elem` [EQ, LT])

  describe "idceiling" $ do
    it "returns an element belonging to set" $ property $
        \((d::dim), i) ->
            fmap ((idelem d) . unQ) (idceiling d i) == Just True

    it "returns an element greater or EQ" $ property $
        \((d::dim), i) ->
            fmap ((`elem` [GT,EQ]) . (`compare` i) . unQ) (idceiling d i)
              == Just True

    it "application preserves ordering" $ property $
        \((d::dim), (a,b,c)) ->
          let fa'     = idceiling d a
              fb'     = idceiling d b
              fc'     = idceiling d c
              Just fa = fa'
              Just fb = fb'
              Just fc = fc'
          in a > b && b > c && isJust fa' && isJust fb' && isJust fc'  ==>
            ((fa `compare` fb) `elem` [EQ, GT])
              &&
            ((fb `compare` fc) `elem` [EQ, GT])
              &&
            ((fa `compare` fc) `elem` [EQ, GT])

  describe "idenumUp" $ do

    it "returns only elements of dimension" $ property $
        \((d::dim), i) ->
            all ((idelem d) . unQ) $ takeSample $ idenumUp d i

    it "returns sorted elements" $ property $
        \((d::dim), i) ->
            let elems = takeSample $ idenumUp d i
            in L.sort elems == elems

    it "does not return duplicate elements" $ property $
        \((d::dim), i) ->
            let elems = takeSample $ idenumUp d i
            in L.nub elems == elems


  describe "idenumDown" $ do

    it "returns only elements of dimension" $ property $
        \((d::dim), i) ->
            all ((idelem d) . unQ) $ takeSample $ idenumDown d i

    it "returns reversely sorted elements" $ property $
        \((d::dim), i) ->
            let elems = takeSample $ idenumDown d i
            in L.sort elems == reverse elems

    it "does not return duplicate elements" $ property $
        \((d::dim), i) ->
            let elems = takeSample $ idenumUp d i
            in L.nub elems == elems


-- Utilidades

datetime :: Int -> Int -> Int -> Int -> Int -> UTCTime
datetime y m d h mn
  = UTCTime (fromGregorian (fromIntegral y) m d) (fromIntegral (h*60+mn)*60)

data Proxy a = Proxy


-- A continuación se implementan instancias de Arbitrary de varios tipos
-- para poder generar valores aleatorios para tests de propiedades
instance Arbitrary ForecastTime where
    arbitrary = fromUTCTime <$> arbitrary

instance Arbitrary RunTime where
    arbitrary = fromUTCTime <$> arbitrary

instance Arbitrary ObservationTime where
    arbitrary = fromUTCTime <$> arbitrary

instance Arbitrary Day where
    arbitrary = ModifiedJulianDay . fromIntegral <$> choose (day0, day1)
      where
        ModifiedJulianDay day0 = fromGregorian 0 1 1
        ModifiedJulianDay day1 = fromGregorian 5000 1 1

instance Arbitrary UTCTime where
    arbitrary
      = UTCTime <$> arbitrary
                <*> (fromIntegral <$> (choose (0, 24*3600-1) :: Gen Int))

instance (Arbitrary a, Arbitrary b) => Arbitrary (a :* b) where
    arbitrary = (:*) <$> arbitrary <*> arbitrary

instance (Arbitrary a, Arbitrary b) => Arbitrary (a :~ b) where
    arbitrary = (:~) <$> arbitrary <*> arbitrary

instance Arbitrary Horizons where
    arbitrary = fromList <$> listOf1 arbitrary

instance Arbitrary Horizon where
    arbitrary = oneof [ Minute <$> choose (-10000,10000)
                      , Hour   <$> choose (-10000,10000)
                      , Day    <$> choose (-1000,1000)]

instance Arbitrary (Schedule t) where
    arbitrary = Schedule <$> arbitrary

isParseable :: CronSchedule -> Bool
isParseable (CronSchedule a b c d e) = isRight p
  where p = parseOnly cronSchedule $ fromString s
        s = unwords [show a, show b, show c, show d, show e]

instance Arbitrary CronSchedule where
    arbitrary = cronschedule >>= \s -> if isValid s then return s else arbitrary
      where
        isValid  = isParseable
        cronschedule = CronSchedule <$> arbitrary
                                    <*> arbitrary
                                    <*> arbitrary
                                    <*> arbitrary
                                    <*> pure (DaysOfWeek Star) --TODO

instance Arbitrary DayOfWeekSpec where
    arbitrary = DaysOfWeek <$> arbitraryCronField (0,7)
instance Arbitrary DayOfMonthSpec where
    arbitrary = DaysOfMonth <$> arbitraryCronField (1,28)
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
                       listOf1 (oneof [ star
                                      , specificField
                                      , rangeField
                                      , stepField])
    stepField     = StepField  <$> oneof [star]--,rangeField]
                               <*> choose ( max 1 (fst range)
                                          , snd range)
