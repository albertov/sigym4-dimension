{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE ScopedTypeVariables
           , TypeFamilies
           , TypeOperators
           , RecordWildCards
           #-}
module Sigym4.Dimension.CronSchedule (
   CronSchedule (..)
 ) where

import Data.Attoparsec.Text (parseOnly)
import Data.String (IsString(fromString))
import Data.Maybe (catMaybes)
import System.Cron
import System.Cron.Parser (cronSchedule)
import Data.Time.Clock (UTCTime(..))
import Data.Time.Calendar          (toGregorian, fromGregorian
                                   , Day(ModifiedJulianDay))
import Data.Time.Calendar.Julian   (isJulianLeapYear)
-- import Data.Time.Calendar.WeekDate (toWeekDate)
import Data.Time.LocalTime         (TimeOfDay(..), timeToTimeOfDay)

import Sigym4.Dimension.Types

instance IsString CronSchedule where
    fromString s = case parseOnly cronSchedule (fromString s) of
                     Right r -> r
                     Left  e -> error $ "fromString(CronSchedule): " ++ e

instance Dimension CronSchedule where
    type DimensionIx CronSchedule = UTCTime
    delem      = flip scheduleMatches
    dpred    s = fmap dimIxToTime . dpred    (scheduleToDim s) . timeToDimIx
    dsucc    s = fmap dimIxToTime . dsucc    (scheduleToDim s) . timeToDimIx
    dfloor   s = fmap dimIxToTime . dfloor   (scheduleToDim s) . timeToDimIx
    dceiling s = fmap dimIxToTime . dceiling (scheduleToDim s) . timeToDimIx

instance Dimension CronField where
    type DimensionIx CronField = Int

    -- delem
    delem _ Star                           = True
    delem m (SpecificField i)              = m==i
    delem m (RangeField a b)               = a<=m && m<=b
    delem m (ListField fs)                 = any (delem m) fs
    delem m (StepField Star s)             = m `mod` s == 0
    delem m (StepField (RangeField a b) s) = a<=m && m<=b && (m-a) `mod` s == 0
    delem _ f@(StepField _ _)
      = error $ "delem(CronField): Unimplemented " ++ show f

    -- dpred
    dpred Star                            m = Just (m-1)
    dpred (SpecificField i)               m | m<=i      = Nothing
                                            | otherwise = Just i
    dpred (RangeField a b)                m | b   <= m  = Just (b-1)
                                            | m-1 >= a  = Just (m-1)
                                            | otherwise = Nothing
    dpred (ListField fs)                  m | isEl      = dpred f m
                                            | otherwise = maxPred
      where
        isEls   = zip (map (delem m) fs) fs
        isEl    = any fst isEls
        f       = snd . head . dropWhile fst $ isEls
        preds   = map (`dpred` m) fs
        maxPred = case catMaybes preds of
                    [] -> Nothing
                    ps -> Just . maximum .filter (<m) $ ps
    dpred (StepField Star s)              m = Just $ m - (m `mod` s) - s
    dpred (StepField (RangeField a b) s)  m | a<=m' && m'<=b = Just m'
                                            | otherwise      = Nothing
      where m' = m - (m `mod` s) - s
    dpred f@(StepField _ _)               _
      = error $ "dpred(CronField): Unimplemented " ++ show f

    -- dsucc
    dsucc Star                            m = Just (m+1)
    dsucc (SpecificField i)               m | m>=i      = Nothing
                                            | otherwise = Just i
    dsucc (RangeField a b)                m | m   <= a  = Just (a+1)
                                            | m+1 <= b  = Just (m+1)
                                            | otherwise = Nothing
    dsucc (ListField fs)                  m = let succs = map (`dsucc` m) fs
                                              in case catMaybes succs of
                                                [] -> Nothing
                                                ps -> Just $ minimum ps
    dsucc (StepField Star s)              m = Just $ m - (m `mod` s) + s
    dsucc (StepField (RangeField a b) s)  m | a<=m' && m'<=b = Just m'
                                            | otherwise      = Nothing
      where m' = m - (m `mod` s) + s
    dsucc f@(StepField _ _)               _
      = error $ "dsucc(CronField): Unimplemented " ++ show f
    
    -- dfloor
    dfloor Star                            m = Just m
    dfloor (SpecificField i)               m | m>=i         = Just i
                                             | otherwise    = Nothing
    dfloor (RangeField a b)                m | a<=m && m<=b = Just m
                                             | m>b          = Just b
                                             | otherwise    = Nothing
    dfloor (ListField fs)                  m = let floors = map (`dfloor` m) fs
                                               in case catMaybes floors of
                                                 [] -> Nothing
                                                 ps -> Just $ maximum ps
    dfloor (StepField Star s)              m = Just $ m - (m `mod` s)
    dfloor (StepField (RangeField a b) s)  m | a<=m' && m'<=b = Just m'
                                             | m'>b           = Just b
                                             | otherwise      = Nothing
      where m' = m - (m `mod` s)
    dfloor f@(StepField _ _)               _
      = error $ "dfloor(CronField): Unimplemented " ++ show f

    -- dceiling
    dceiling Star                            m = Just m
    dceiling (SpecificField i)               m | m<=i         = Just i
                                               | otherwise    = Nothing
    dceiling (RangeField a b)                m | a<=m && m<=b = Just m
                                               | m<a          = Just a
                                               | otherwise    = Nothing
    dceiling (ListField fs)                  m = let cs = map (`dceiling` m) fs
                                              in case catMaybes cs of
                                                [] -> Nothing
                                                ps -> Just $ minimum ps
    dceiling (StepField Star s)              m | md == 0   = Just m
                                               | otherwise = Just $ m + (s-md)
      where md = m `mod` s
    dceiling (StepField (RangeField a b) s)  m | a<=m' && m'<=b = Just m'
                                               | otherwise      = Nothing
      where m' = if md==0 then m else m + (s-md)
            md = m `mod` s
    dceiling f@(StepField _ _)               _
      = error $ "dceiling(CronField): Unimplemented " ++ show f

instance BoundedDimension CronField where
    type Dependent CronField  = ()
    dfirst Star                           = const 0
    dfirst (SpecificField i)              = const i
    dfirst (RangeField a _)               = const a
    dfirst (ListField fs)                 = const $ minimum
                                          $ map (\f -> dfirst f undefined) fs
    dfirst (StepField Star _)             = const 0
    dfirst (StepField (RangeField a _) s) = const (a `div` s * (s+1))
    dfirst f@(StepField _ _)
      = const $ error $ "dfirst(CronField): Unimplemented " ++ show f
    dlast  _ _ = 59

instance Dimension MinuteSpec where
    type DimensionIx MinuteSpec = Int
    delem i  (Minutes cs) = 0<=i && i<=59 && i `delem` cs
    dpred    (Minutes cs) = justIfInRange 0 59 . dpred    cs
    dsucc    (Minutes cs) = justIfInRange 0 59 . dsucc    cs
    dfloor   (Minutes cs) = justIfInRange 0 59 . dfloor   cs
    dceiling (Minutes cs) = justIfInRange 0 59 . dceiling cs

justIfInRange :: Int -> Int -> Maybe Int -> Maybe Int
justIfInRange lo hi (Just i) | lo<=i, i<=hi = Just i
justIfInRange _  _  _                       = Nothing

instance BoundedDimension MinuteSpec where
    type Dependent MinuteSpec = Int
    dfirst _ _ = 0
    dlast  _ _ = 59
    denum  _ _ = [0..59]

instance Dimension HourSpec where
    type DimensionIx HourSpec = Int
    delem i  (Hours cs) = 0<=i && i<=23 && i `delem` cs
    dpred    (Hours cs) = justIfInRange 0 23 . dpred    cs
    dsucc    (Hours cs) = justIfInRange 0 23 . dsucc    cs
    dfloor   (Hours cs) = justIfInRange 0 23 . dfloor   cs
    dceiling (Hours cs) = justIfInRange 0 23 . dceiling cs

instance BoundedDimension HourSpec where
    type Dependent HourSpec = Int
    dfirst _ _ = 0
    dlast  _ _ = 23
    denum  _ _ = [0..23]

-- | BoundedDimension instance will perform further bounds checking
instance Dimension DayOfMonthSpec where
    type DimensionIx DayOfMonthSpec = Int
    delem i  (DaysOfMonth cs) = 1<=i && i<=31 && i `delem` cs
    dpred    (DaysOfMonth cs) = justIfInRange 1 31 . dpred    cs
    dsucc    (DaysOfMonth cs) = justIfInRange 1 31 . dsucc    cs
    dfloor   (DaysOfMonth cs) = justIfInRange 1 31 . dfloor   cs
    dceiling (DaysOfMonth cs) = justIfInRange 1 31 . dceiling cs

instance BoundedDimension DayOfMonthSpec where
    type Dependent DayOfMonthSpec = Int :> Int
    dfirst _ (mth :> yr)
      | mth == minMonth, yr  == minYear    = minDay
      | otherwise                          = 1
    dlast  _ (mth :> yr) = daysPerMonth yr mth

daysPerMonth :: Int -> Int -> Int
daysPerMonth yr mth
  | mth == 2, isLeapYear yr       = 29
  | mth == 2                      = 28
  | mth `elem` [4,6,9,11]         = 30
  | otherwise                     = 31
  where isLeapYear = isJulianLeapYear . fromIntegral

instance Dimension MonthSpec where
    type DimensionIx MonthSpec = Int
    delem i  (Months cs) = 1<=i && i<=12 && i `delem` cs
    dpred    (Months cs) = justIfInRange 1 12 . dpred    cs
    dsucc    (Months cs) = justIfInRange 1 12 . dsucc    cs
    dfloor   (Months cs) = justIfInRange 1 12 . dfloor   cs
    dceiling (Months cs) = justIfInRange 1 12 . dceiling cs

instance BoundedDimension MonthSpec where
    type Dependent MonthSpec = Int
    dfirst _ yr | yr == minYear = minMonth
                | otherwise     = 1
    dlast  _ _ = 12
    denum  _ _ = [1..12]

instance Dimension Years where
    type DimensionIx Years = Int
    delem i  (Years a b) = a<=i && i<=b
    dpred    (Years a b) = justIfInRange a b . Just
    dsucc    (Years a b) = justIfInRange a b . Just
    dfloor   (Years a b) = justIfInRange a b . Just
    dceiling (Years a b) = justIfInRange a b . Just

{-
instance BoundedDimension Years where
    type Dependent Years = ()
    dfirst (Years a _) _ = a
    dlast  (Years _ b) _ = b
-}

type TimeIx = DimensionIx CronScheduleDim
type CronScheduleDim = MinuteSpec
                    :> HourSpec
                    :> DayOfMonthSpec 
                    :> (MonthSpec :> Years)
data Years = Years !Int !Int

dimIxToTime :: TimeIx -> UTCTime
dimIxToTime (mins :> hours :> dom :> (month :> year))
  = UTCTime (fromGregorian (fromIntegral year) month dom)
            (fromIntegral $ (hours*60+mins) * 60)

timeToDimIx :: UTCTime -> TimeIx
timeToDimIx UTCTime {utctDay = uDay, utctDayTime = uTime }
  = mn :> hr :> dom :> (mth :> fromIntegral yr)
  where (yr, mth, dom) = toGregorian uDay
        --(_, _, dow)    = toWeekDate uDay
        TimeOfDay { todHour = hr, todMin  = mn} = timeToTimeOfDay uTime

scheduleToDim :: CronSchedule -> CronScheduleDim
scheduleToDim CronSchedule{..}
    = minute :> hour :> dayOfMonth :> (month :> Years minYear 5000)

minYear' :: Integer
minYear, minMonth, minDay :: Int
minYear = fromIntegral minYear'
(minYear', minMonth, minDay) = toGregorian (ModifiedJulianDay  0)
