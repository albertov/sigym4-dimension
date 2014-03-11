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
import Data.Time.Calendar          (toGregorian, fromGregorian, isLeapYear)
-- import Data.Time.Calendar.WeekDate (toWeekDate)
import Data.Time.LocalTime         (TimeOfDay(..), timeToTimeOfDay)

import Sigym4.Dimension.Types

instance IsString CronSchedule where
    fromString s = case parseOnly cronSchedule (fromString s) of
                     Right r -> r
                     Left  e -> error $ "fromString(CronSchedule): " ++ e

instance Dimension CronSchedule where
    type DimensionIx CronSchedule = UTCTime
    delem  t s =  timeToDimIx t `delem`  scheduleToDim s
    dpred    s = fmap dimIxToTime . dpred    (scheduleToDim s) . timeToDimIx
    dsucc    s = fmap dimIxToTime . dsucc    (scheduleToDim s) . timeToDimIx
    dfloor   s = fmap dimIxToTime . dfloor   (scheduleToDim s) . timeToDimIx
    dceiling s = fmap dimIxToTime . dceiling (scheduleToDim s) . timeToDimIx

data BCronField = CF CronField Int Int deriving Show

instance Dimension BCronField where
    type DimensionIx BCronField = Int

    -- delem
    delem m (CF Star               lo hi)               = lo<=m && m<=hi
    delem m (CF (SpecificField i)  _  _ )               = m==i
    delem m (CF (RangeField a b)   lo hi)               = max lo a <= m 
                                                       && min hi b >= m
    delem m (CF (ListField fs)     lo hi)               = any (delem m)
                                                          [CF f lo hi | f<-fs]
    delem m (CF (StepField Star s) lo hi)               = lo<=m && m<=hi
                                                       && m `mod` s == 0
    delem m (CF (StepField (RangeField a b) s) lo hi)   = max lo a <= m
                                                       && min hi b >= m
                                                       && m `mod` s == 0
    delem _ (CF f@(StepField _ _) _ _)
      = error $ "delem(BCronField): Unimplemented " ++ show f

    -- dpred
    dpred (CF Star lo hi) m
      | m>=hi     = Just (hi-1)
      | lo<=(m-1) = Just (m-1)
      | otherwise = Nothing

    dpred (CF (SpecificField i) lo _) m
      | m <= max lo i = Nothing
      | otherwise     = Just i

    dpred (CF (RangeField a b) lo hi) m
      | hi' <= m   = Just (hi'-1)
      | m-1 >= lo' = Just (m-1)
      | otherwise  = Nothing
      where
        hi' = min hi b
        lo' = max lo a

    dpred (CF (StepField Star s) lo hi) m
      | m'>= lo   = Just m'
      | m'>= hi   = Just $ hi - s
      | otherwise = Nothing
      where m' = (m `modFloor` s) - s

    dpred (CF (StepField (RangeField a b) s) lo hi) m
      | m'>= lo'   = Just m'
      | m'>= hi'   = Just $ hi' - s
      | otherwise  = Nothing
      where m'  = (m `modFloor` s) - s
            lo' = max lo a
            hi' = min hi b

    dpred (CF (ListField fs') lo hi) m
      | isEl = dpred f m
      | otherwise = maxPred
      where
        fs      = [CF f' lo hi | f'<-fs']
        isEls   = zip (map (delem m) fs) fs
        isEl    = any fst isEls
        f       = snd . head . dropWhile (not.fst) $ isEls
        preds   = map (`dpred` m) fs
        maxPred = case catMaybes preds of
                    [] -> Nothing
                    ps -> Just . maximum .filter (<m) $ ps

    dpred (CF f@(StepField _ _) _ _) _
      = error $ "dpred(CronField): Unimplemented " ++ show f


    -- succ
    dsucc (CF Star lo hi) m
      | m<=lo     = Just (lo+1)
      | hi>=(m+1) = Just (m+1)
      | otherwise = Nothing

    dsucc (CF (SpecificField i) _ hi) m
      | m >= min hi i = Nothing
      | otherwise     = Just i

    dsucc (CF (RangeField a b) lo hi) m
      | lo' >= m    = Just (lo'+1)
      | m+1 <= hi'  = Just (m+1)
      | otherwise   = Nothing
      where
        lo' = max lo a
        hi' = min hi b

    dsucc (CF (StepField Star s) lo hi) m
      | m'<= hi   = Just m'
      | m'<= lo   = Just $ lo + s
      | otherwise = Nothing
      where m' = (m `modCeil` s) + s

    dsucc (CF (StepField (RangeField a b) s) lo hi) m
      | m'<= hi'   = Just m'
      | m'<= lo'   = Just $ lo' + s
      | otherwise  = Nothing
      where m'  = (m `modCeil` s) + s
            lo' = max lo a
            hi' = min hi b

    dsucc (CF (ListField fs') lo hi) m
      | isEl      = dsucc f m
      | otherwise = minSucc
      where
        fs      = [CF f' lo hi | f'<-fs']
        isEls   = zip (map (delem m) fs) fs
        isEl    = any fst isEls
        f       = snd . head . dropWhile (not.fst) $ isEls
        succs   = map (`dsucc` m) fs
        minSucc = case catMaybes succs of
                    [] -> Nothing
                    ps -> Just . minimum .filter (>m) $ ps

    dsucc (CF f@(StepField _ _) _ _) _
      = error $ "dsucc(CronField): Unimplemented " ++ show f
    
    -- dfloor
    dfloor (CF Star lo hi) m
      | m>hi      = Just hi
      | lo<=m     = Just m
      | otherwise = Nothing

    dfloor (CF (SpecificField i) lo hi) m
      | m <  max lo i = Nothing
      | otherwise     = Just $ min hi i

    dfloor (CF (RangeField a b) lo hi) m
      | hi' <= m   = Just hi'
      | m   >= lo' = Just m
      | otherwise  = Nothing
      where
        hi' = min hi b
        lo' = max lo a

    dfloor (CF (StepField Star s) lo hi) m
      | m'>= lo, m'<=hi = Just m'
      | m' >hi          = Just hi
      | otherwise       = Nothing
      where m' = m `modFloor` s

    dfloor (CF (StepField (RangeField a b) s) lo hi) m
      | lo'<=m' && m'<=hi' = Just m'
      | m' >hi'            = Just hi'
      | otherwise          = Nothing
      where m' = m `modFloor` s
            lo' = max lo a
            hi' = min hi b

    dfloor (CF (ListField fs') lo hi) m
      | isEl      = dfloor f m
      | otherwise = maxFloor
      where
        fs       = [CF f' lo hi | f'<-fs']
        isEls    = zip (map (delem m) fs) fs
        isEl     = any fst isEls
        f        = snd . head . dropWhile (not.fst) $ isEls
        floors   = map (`dpred` m) fs
        maxFloor = case catMaybes floors of
                     [] -> Nothing
                     ps -> Just . maximum .filter (<=m) $ ps

    dfloor (CF f@(StepField _ _) _ _) _
      = error $ "dfloor(CronField): Unimplemented " ++ show f
    
    -- dceiling
    dceiling (CF Star lo hi) m
      | m<lo      = Just lo
      | hi>=m     = Just m
      | otherwise = Nothing

    dceiling (CF (SpecificField i) lo hi) m
      | m >  min hi i = Nothing
      | otherwise     = Just $ max lo i

    dceiling (CF (RangeField a b) lo hi) m
      | lo' >= m    = Just lo'
      | m   <= hi'  = Just m
      | otherwise   = Nothing
      where
        lo' = max lo a
        hi' = min hi b

    dceiling (CF (StepField Star s) lo hi) m
      | m'<=lo    = Just lo
      | m'<=hi    = Just m'
      | otherwise = Nothing
      where m' = m `modCeil` s

    dceiling (CF (StepField (RangeField a b) s) lo hi) m
      | m'<=lo'   = Just lo
      | m'<=hi'   = Just m'
      | otherwise = Nothing
      where m'  = m `modCeil` s
            lo' = max lo a
            hi' = min hi b

    dceiling (CF (ListField fs') lo hi) m
      | isEl      = dceiling f m
      | otherwise = minCeil
      where
        fs      = [CF f' lo hi | f'<-fs']
        isEls   = zip (map (delem m) fs) fs
        isEl    = any fst isEls
        f       = snd . head . dropWhile (not.fst) $ isEls
        ceils   = map (`dceiling` m) fs
        minCeil = case catMaybes ceils of
                    [] -> Nothing
                    ps -> Just . minimum .filter (>=m) $ ps

    dceiling (CF f@(StepField _ _) _ _) _
      = error $ "dceiling(CronField): Unimplemented " ++ show f

instance BoundedDimension BCronField where
    type Dependent BCronField = ()
    dfirst (CF Star                           lo _ ) = const lo
    dfirst (CF (SpecificField i)              lo _ ) = const $ max lo i
    dfirst (CF (RangeField a _)               lo _ ) = const $ max lo a
    dfirst (CF (ListField fs)                 lo hi)
      = const $ minimum $ map (\f -> dfirst (CF f lo hi) undefined) fs
    dfirst (CF (StepField Star s)             lo _ ) = const (lo `modCeil` s)
    dfirst (CF (StepField (RangeField a _) s) lo _ ) = const (lo' `modCeil` s)
        where lo' = max lo a
    dfirst (CF f@(StepField _ _)              _  _ )
      = const $ error $ "dfirst(CronField): Unimplemented " ++ show f

    dlast  (CF Star                           _  hi) = const hi
    dlast  (CF (SpecificField i)              _  hi) = const $ min hi i
    dlast  (CF (RangeField _ b)               _  hi) = const $ min hi b
    dlast  (CF (ListField fs)                 lo hi)
      = const $ maximum $ map (\f -> dfirst (CF f lo hi) undefined) fs
    dlast  (CF (StepField Star s)             _  hi) = const (hi `modFloor` s)
    dlast  (CF (StepField (RangeField _ b) s) _  hi) = const (hi' `modFloor` s)
        where hi' = min hi b
    dlast  (CF f@(StepField _ _)              _  _ )
      = const $ error $ "dlast(CronField): Unimplemented " ++ show f

modFloor, modCeil :: Integral a => a -> a -> a
modFloor a m = a - (a `mod` m)
modCeil  a m
  | md == 0   = a
  | otherwise = a + (m-md)
  where md = a `mod` m

instance Dimension MinuteSpec where
    type DimensionIx MinuteSpec = Int
    delem i  (Minutes cs) = i `delem` (CF cs 0 59)
    dpred    (Minutes cs) = dpred     (CF cs 0 59)
    dsucc    (Minutes cs) = dsucc     (CF cs 0 59)
    dfloor   (Minutes cs) = dfloor    (CF cs 0 59)
    dceiling (Minutes cs) = dceiling  (CF cs 0 59)

instance BoundedDimension MinuteSpec where
    type Dependent MinuteSpec = Int
    dfirst (Minutes cs) _ = dfirst (CF cs 0 59) ()
    dlast  (Minutes cs) _ = dlast  (CF cs 0 59) ()

instance Dimension HourSpec where
    type DimensionIx HourSpec = Int
    delem i  (Hours cs) = i `delem` (CF cs 0 23)
    dpred    (Hours cs) = dpred     (CF cs 0 23)
    dsucc    (Hours cs) = dsucc     (CF cs 0 23)
    dfloor   (Hours cs) = dfloor    (CF cs 0 23)
    dceiling (Hours cs) = dceiling  (CF cs 0 23)

instance BoundedDimension HourSpec where
    type Dependent HourSpec = Int
    dfirst (Hours cs) _ = dfirst (CF cs 0 23) ()
    dlast  (Hours cs) _ = dlast  (CF cs 0 23) ()

instance Dimension DayOfMonthSpec where
    type DimensionIx DayOfMonthSpec = Int
    delem i  (DaysOfMonth cs) = i `delem` (CF cs 1 31)
    dpred    (DaysOfMonth cs) = dpred     (CF cs 1 31)
    dsucc    (DaysOfMonth cs) = dsucc     (CF cs 1 31)
    dfloor   (DaysOfMonth cs) = dfloor    (CF cs 1 31)
    dceiling (DaysOfMonth cs) = dceiling  (CF cs 1 31)

instance BoundedDimension DayOfMonthSpec where
    type Dependent DayOfMonthSpec = Int :> Int
    dfirst (DaysOfMonth cs) (mth :> yr) = dfirst (CF cs 1 dpm) ()
      where dpm = daysPerMonth yr mth
    dlast  (DaysOfMonth cs) (mth :> yr) = dlast  (CF cs 1 dpm) ()
      where dpm = daysPerMonth yr mth

daysPerMonth :: Int -> Int -> Int
daysPerMonth yr mth
  | mth == 2, isLeapYear' yr       = 29
  | mth == 2                      = 28
  | mth `elem` [4,6,9,11]         = 30
  | otherwise                     = 31
  where isLeapYear' = isLeapYear . fromIntegral

instance Dimension MonthSpec where
    type DimensionIx MonthSpec = Int
    delem i  (Months cs) = i `delem` (CF cs 1 12)
    dpred    (Months cs) = dpred     (CF cs 1 12)
    dsucc    (Months cs) = dsucc     (CF cs 1 12)
    dfloor   (Months cs) = dfloor    (CF cs 1 12)
    dceiling (Months cs) = dceiling  (CF cs 1 12)

instance BoundedDimension MonthSpec where
    type Dependent MonthSpec = Int
    dfirst (Months cs) _  = dfirst (CF cs  1 12) ()
    dlast  (Months cs) _  = dlast  (CF cs  1 12) ()

instance Dimension Years where
    type DimensionIx Years = Int
    delem    _ _ = True
    dpred    _ i = Just (i-1)
    dsucc    _ i = Just (i+1)
    dfloor   _ i = Just i
    dceiling _ i = Just i

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
data Years = Years

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
    = minute :> hour :> dayOfMonth :> (month :> Years)
