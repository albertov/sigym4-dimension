{-# LANGUAGE ScopedTypeVariables #-}
module Sigym4.DimensionSpec (main, spec) where
import Control.Applicative
import Test.Hspec
import Test.Hspec.QuickCheck
import Sigym4.Dimension
import Data.Time.Calendar
import Data.Time.Clock
import Test.QuickCheck
import System.Cron

main :: IO ()
main = hspec spec

spec :: Spec
spec = do
  describe "denumUp" $ do
    it "returns only elements of dimension" $ property $
        \((d::Schedule ObservationTime), i) ->
            all (`delem` d) $ take 100 $ denumUp d i

instance Arbitrary ObservationTime where
    arbitrary = fromUTCTime <$> arbitrary

instance Arbitrary UTCTime where
    arbitrary
      = UTCTime <$> (ModifiedJulianDay <$> arbitrary)
                <*> (fromIntegral      <$> (arbitrary :: Gen (NonNegative Int)))

instance Arbitrary (Schedule t) where
    arbitrary = Schedule <$> arbitrary

instance Arbitrary CronSchedule where
    arbitrary = CronSchedule <$> arbitrary
                             <*> arbitrary
                             <*> pure (DaysOfMonth Star)
                             <*> pure (Months Star)
                             <*> pure (DaysOfWeek Star)

instance Arbitrary DayOfWeekSpec where
    arbitrary = DaysOfWeek <$> pure Star -- FIXME
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
    stepField     = StepField  <$> star <*> choose (1,snd range)
