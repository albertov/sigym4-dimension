{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE OverloadedStrings
           , TemplateHaskell
           , ScopedTypeVariables
           , QuasiQuotes
           , TypeOperators
           , TypeFamilies
           , FlexibleContexts
           , FlexibleInstances
           , TypeSynonymInstances
           , UndecidableInstances
           , ViewPatterns
           #-}
module Sigym4.DimensionSpec (main, spec) where

import Sigym4.Dimension
import Sigym4.Dimension.Time
import Sigym4.Dimension.CronSchedule

import System.Cron hiding (Schedule)
import System.Cron.Parser (cronSchedule)

import Control.Applicative
import Control.Newtype
import Test.Hspec
import Data.Time.Calendar
import Data.Time.Calendar.WeekDate (toWeekDate)
import Data.Time.Clock
import qualified Data.List as L
import qualified Data.Set as S
import Data.Maybe (isJust, fromJust)
import Data.Either (isRight)
import Data.String (fromString)
import Data.Proxy
import Data.Attoparsec.Text (parseOnly)
import Test.QuickCheck
import GHC.Exts (fromList)
import Debug.Trace

main :: IO ()
main = hspec spec

sampleLen :: Int
sampleLen = 500

takeSample :: [a] -> [a]
takeSample = take sampleLen

spec :: Spec
spec = do
  dimensionSpec "Infinite Int" (Proxy :: Proxy (Infinite Int))

  dimensionSpec "Schedule ObservationTime"
                (Proxy :: Proxy (Schedule ObservationTime))

  dimensionSpec "Horizons" (Proxy :: Proxy Horizons)

  dimensionSpec "Horizons :* Schedule RunTime"
                (Proxy :: Proxy (Horizons :* Schedule RunTime))

  context "CronSchedule" $ do
    {- El modélo está mal. No trata el 0 como domingo
    describe "idelem" $ do
      it "behaves like model" $ property $
        \(s, t) -> s `idelem` t == s `scheduleMatches` t
    -}

    describe "idfloor" $ do
      it "does not crash on impossible schedule" $ do
        let sched = [cron|0 0 31 2 *|]
        idfloor sched (datetime 2012 3 1 0 0) `shouldBe` Nothing

      it "handles corner case" $ do
        let sched = [cron|31 */21 6-31 */3 1|]
            t1    = datetime 2115 06 28 21 48
            t2    = datetime 2115 08 30 20 54
            ft1   = idfloor sched t1
            ft2   = idfloor sched t2
        ft1 <= ft2


    describe "leap years" $ do
      it "returns only feb 29" $ do
        let d  = [intrtq|20080229/P4Y|]
            Just t = idfloor d (datetime 2012 3 1 0 0)
        unQ t `shouldBe` (datetime 2012 2 29 0 0  :: RunTime)
        fmap unQ (idsucc d t) `shouldBe` Just (datetime 2016 2 29 0 0)
        fmap unQ (idpred d t) `shouldBe` Just (datetime 2008 2 29 0 0)

      it "returns only feb 29 on monday" $ do
        let sched     = [cron|0 0 29 2 1|]
            matches (UTCTime d _) = let (_,m,dom) = toGregorian d
                                        (_,_,dow) = toWeekDate d
                                    in dow == 1 && m==2 && dom==29
            ts = takeSample . map unQ . idenumUp sched $ datetime 2012 3 1 0 0
                              
        length ts `shouldBe` sampleLen
        all  matches ts `shouldBe` True

      describe "idsucc" $ do
        it "returns day 29" $ do
          let sched  = [cron|0 0 * * *|]
              Just t = idfloor sched (datetime 2012 2 28 0 0)
              Just s = idsucc sched t
          unQ s `shouldBe` datetime 2012 2 29 0 0
        it "accepts day 29" $ do
          let sched  = [cron|0 0 * * *|]
              Just t = idfloor sched (datetime 2012 2 29 0 0)
              Just s = idsucc sched t
          unQ s `shouldBe` datetime 2012 3 1 0 0

      describe "idpred" $ do
        it "returns day 29" $ do
          let sched  = [cron|0 0 * * *|]
              Just t = idfloor sched (datetime 2012 3 1 0 0)
              Just s = idpred sched t
          unQ s `shouldBe` datetime 2012 2 29 0 0
        it "accepts day 29" $ do
          let sched  = [cron|0 0 * * *|]
              Just t = idfloor sched (datetime 2012 2 29 0 0)
              Just s = idpred sched t
          unQ s `shouldBe` datetime 2012 2 28 0 0
             

-- | Una especificación que comprueba que se cumplen las propiedades de
--   'Dimension' en cualquier instancia.
dimensionSpec :: forall dim.
  ( Show dim, Eq dim, Show (DimensionIx dim), Arbitrary dim, Arbitrary (DimensionIx dim), Dimension dim
  , Dependent dim ~ ())
  => String -> Proxy dim -> Spec
dimensionSpec typeName _ = context ("Dimension ("++typeName++")") $ do
  describe "idsucc" $ do
    it "returns an element strictly greater" $ property $ \(d::dim, i) ->
      let c      = idceiling d i
          f      = idsucc d (fromJust c)
          Just v = f
      in isJust c && isJust f ==>
        counterexample (show (d,i,c)) $
          unQ v > i

    it "application preserves ordering" $ property $
        \(d::dim, getOrdered -> elems) ->
          let (c:b:a:_) = elems
              fa'     = idceiling d a
              fb'     = idceiling d b
              fc'     = idceiling d c
              fa''    = idsucc d =<< fa'
              fb''    = idsucc d =<< fb'
              fc''    = idsucc d =<< fc'
              Just fa = fa''
              Just fb = fb''
              Just fc = fc''
          in length elems >= 3 && isJust fa'' && isJust fb'' && isJust fc'' ==>
              (fa >= fb) && (fb >= fc) && (fa >= fc)

  describe "idpred" $ do

    it "returns an element strictly smaller" $ property $ \(d::dim, i) ->
      let c      = idfloor d i
          f      = idpred d (fromJust c)
          Just v = f
      in isJust c && isJust f ==>
        counterexample (show (d,i,c)) $ unQ v < i

    it "application preserves ordering" $ property $
        \(d::dim, getOrdered -> elems) ->
          let (a:b:c:_) = elems
              fa'     = idfloor d a
              fb'     = idfloor d b
              fc'     = idfloor d c
              fa''    = idpred d =<< fa'
              fb''    = idpred d =<< fb'
              fc''    = idpred d =<< fc'
              Just fa = fa''
              Just fb = fb''
              Just fc = fc''
          in length elems >= 3 && isJust fa'' && isJust fb'' && isJust fc'' ==>
              (fa <= fb) && (fb <= fc) && (fa <= fc)


  describe "idfloor" $ do
    it "returns an element belonging to set" $ property $ \((d::dim), i) ->
      let c = idfloor d i in isJust c ==>
        counterexample (show (d,i,c)) $
          idelem d (unQ (fromJust c))

    it "returns an element <=" $ property $ \(d::dim, i) ->
      let c = idfloor d i in isJust c ==>
        counterexample (show (d,i,c)) $ unQ (fromJust c) <= i

    it "application preserves ordering" $ property $
        \(d::dim, getOrdered -> elems) ->
          let (a:b:c:_) = elems
              fa'     = idfloor d a
              fb'     = idfloor d b
              fc'     = idfloor d c
              Just fa = fa'
              Just fb = fb'
              Just fc = fc'
          in length elems > 2 && isJust fa' && isJust fb' && isJust fc'  ==>
            (fa <= fb) && (fb <= fc) && (fa <= fc)

  describe "idceiling" $ do
    it "returns an element belonging to set" $ property $ \(d::dim, i) ->
      let c = idceiling d i in isJust c ==>
        counterexample (show (d,i,c)) $
          idelem d (unQ (fromJust c))

    it "returns an element GT or EQ" $ property $ \(d::dim, i) ->
      let c = idceiling d i in isJust c ==>
        counterexample (show (d,i,c)) $
          (unQ (fromJust c) `compare` i) `elem` [GT,EQ]

    it "application preserves ordering" $ property $ \(d::dim, (a,b,c)) ->
          let fa'     = idceiling d a
              fb'     = idceiling d b
              fc'     = idceiling d c
              Just fa = fa'
              Just fb = fb'
              Just fc = fc'
          in a >= b && b >= c && isJust fa' && isJust fb' && isJust fc'  ==>
            (fa >= fb) && (fb >= fc) && (fa >= fc)

  describe "idenumUp" $ do

    it "returns only elements of dimension" $ property $
        \(d::dim, i) ->
            let elems = takeSample $ idenumUp d i
            in not (null elems) ==> all ((idelem d) . unQ) elems

    it "returns sorted elements" $ property $
        \(d::dim, i) ->
            let elems = takeSample $ idenumUp d i
            in L.sort elems == elems

    it "does not return duplicate elements" $ property $
        \(d::dim, i) ->
            let elems = takeSample $ idenumUp d i
            in nub elems == elems


  describe "idenumDown" $ do

    it "returns only elements of dimension" $ property $
        \(d::dim, i) ->
            let elems = takeSample $ idenumDown d i
            in not (null elems) ==> all ((idelem d) . unQ) elems

    it "returns reversely sorted elements" $ property $
        \(d::dim, i) ->
            let elems = takeSample $ idenumDown d i
            in L.sort elems == reverse elems

    it "does not return duplicate elements" $ property $
        \(d::dim, i) ->
            let elems = takeSample $ idenumUp d i
            in nub elems == elems


-- Utilidades


-- A continuación se implementan instancias de Arbitrary de varios tipos
-- para poder generar valores aleatorios para tests de propiedades
instance Arbitrary a => Arbitrary (Infinite a) where
    arbitrary = return Inf

instance Arbitrary ForecastTime where
    arbitrary = ForecastTime <$> arbitrary

instance Arbitrary RunTime where
    arbitrary = RunTime <$> arbitrary

instance Arbitrary ObservationTime where
    arbitrary = ObservationTime <$> arbitrary

instance Arbitrary Day where
    arbitrary = arbitraryDayInRange 2010 2020

-- Los años estan cogidos de tal manera que el inicio del intervalo sea menor
-- que los dias arbitrarios ya que si no es dificil generar condiciones validas
-- en los tests de "application preserves ordering"

arbitraryStart :: Newtype t UTCTime => Gen t
arbitraryStart = pack <$> (UTCTime <$> arbitraryDayInRange 2000 2009
                                   <*> arbitraryDT)


arbitraryDayInRange :: Integer -> Integer -> Gen Day
arbitraryDayInRange s e = ModifiedJulianDay . fromIntegral <$> choose (day0, day1)
  where
    ModifiedJulianDay day0 = fromGregorian s 1 1
    ModifiedJulianDay day1 = fromGregorian e 1 1

instance Arbitrary UTCTime where
    arbitrary = UTCTime <$> arbitrary <*> arbitraryDT

arbitraryDT :: Gen DiffTime
arbitraryDT = fromIntegral <$> (choose (0, 24*3600-1) :: Gen Int)

instance (Arbitrary a, Arbitrary b) => Arbitrary (a :* b) where
    arbitrary = (:*) <$> arbitrary <*> arbitrary

instance (Arbitrary a, Arbitrary b) => Arbitrary (a :~ b) where
    arbitrary = (:~) <$> arbitrary <*> arbitrary

instance Arbitrary Horizons where
    arbitrary = do n <- choose (2,100)
                   -- n>=2 pq. si no nunca se cumple la precondición de la prop.
                   fromList <$> vectorOf n arbitrary

instance Arbitrary Horizon where
    arbitrary = oneof [ Minute <$> choose (-1000,1000)
                      , Hour   <$> choose (-1000,1000)
                      , Day    <$> choose (-1000,1000)]


instance Arbitrary DurSecond where arbitrary = DurSecond <$> (getPositive <$> arbitrary)
instance Arbitrary DurMinute where arbitrary = DurMinute <$> choose (5,7200) <*> pure Nothing
instance Arbitrary DurHour   where arbitrary = DurHour   <$> (getPositive <$> arbitrary) <*> arbitrary
instance Arbitrary DurTime   where arbitrary = oneof [ DurTimeHour <$> arbitrary
                                                     , DurTimeMinute <$> arbitrary
                                                     --, DurTimeSecond <$> arbitrary
                                                     ]
instance Arbitrary DurDay   where arbitrary = DurDay   <$> (getPositive <$> arbitrary)
instance Arbitrary DurWeek  where arbitrary = DurWeek  <$> (getPositive <$> arbitrary)
instance Arbitrary DurMonth where arbitrary = DurMonth <$> (getPositive <$> arbitrary) <*> arbitrary
instance Arbitrary DurYear  where arbitrary = DurYear  <$> (getPositive <$> arbitrary) <*> arbitrary
instance Arbitrary DurDate  where arbitrary = oneof [ DurDateDay   <$> arbitrary <*> arbitrary
                                                    , DurDateMonth <$> arbitrary <*> arbitrary
                                                    , DurDateYear  <$> arbitrary <*> arbitrary
                                                    ]
instance Arbitrary Duration where arbitrary = oneof [ DurationDate <$> arbitrary
                                                    , DurationTime <$> arbitrary
                                                    , DurationWeek <$> arbitrary
                                                    ]

instance (Ord t, Newtype t UTCTime, Arbitrary t) => Arbitrary (Interval t) where
  arbitrary = oneof [ validInterval, validBoundedInterval ] where

    validInterval = either (const arbitrary) return
      =<< (interval <$> arbitrary <*> arbitraryStart)

    validBoundedInterval = either (const arbitrary) return
      =<< go where
        go = do p <- arbitrary
                s <- arbitraryStart
                r <- getPositive <$> arbitrary
                let e = iterateDuration p s !! r
                return (boundedInterval p s e)

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
                                    <*> arbitrary

instance Arbitrary DayOfWeekSpec where
    arbitrary = DaysOfWeek <$> arbitraryCronField (1,7)
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
  = oneof [ Field <$> star
          , Field <$> specificField
          , stepField
          , Field <$> rangeField
          , listField
          ]
  where
    specificField :: Gen BaseField
    specificField = SpecificField' . SpecificField <$> choose range

    star :: Gen BaseField
    star = pure Star

    rangeField :: Gen BaseField
    rangeField = do
        lo <- choose range
        hi <- choose range
        if lo<hi
        then return . RangeField' $ RangeField lo hi
        else rangeField

    listField :: Gen CronField
    listField = (ListField . fromList)
            <$> listOf1 (oneof [ star
                               , specificField
                               , rangeField
                               ])

    stepField :: Gen CronField
    stepField = StepField' <$> (StepField  <$> oneof [star, rangeField]
                                           <*> choose ( max 1 (fst range)
                                                      , snd range))


nub :: (Ord a) => [a] -> [a]
nub = go S.empty
  where go _ [] = []
        go s (x:xs) | S.member x s = go s xs
                    | otherwise    = x : go (S.insert x s) xs

