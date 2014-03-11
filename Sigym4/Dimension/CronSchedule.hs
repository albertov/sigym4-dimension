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
import Data.Maybe (catMaybes, fromMaybe, isJust)
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
    type Dependent   CronSchedule = ()
    delem    s _ = idelem (scheduleToDim s) . timeToDimIx
    dpred    s _ = fmap ndimIxToTime . idpred (scheduleToDim s) . ntimeToDimIx
    dsucc    s _ = fmap ndimIxToTime . idsucc (scheduleToDim s) . ntimeToDimIx
    dfloor   s _ = fmap ndimIxToTime . idfloor (scheduleToDim s) . timeToDimIx
    dceiling s _
      = fmap ndimIxToTime . idceiling (scheduleToDim s) . timeToDimIx

data BCronField = CF CronField Int Int deriving Show

instance Dimension BCronField where
    type DimensionIx BCronField = Int
    type Dependent BCronField = ()

    -- delem
    delem (CF Star lo hi) _ m
      = lo<=m && m<=hi
    delem (CF (SpecificField i) _ _) _ m
      = m==i
    delem (CF (RangeField a b) lo hi) _ m
      = max lo a <= m && min hi b >= m
    delem (CF (ListField fs) lo hi) _ m
      = isJust $ firstContaining fs lo hi m
    delem (CF (StepField Star s) lo hi) _ m
      = lo<=m && m<=hi && m `mod` s == 0
    delem (CF (StepField (RangeField a b) s) lo hi) _ m
      = max lo a <= m && min hi b >= m && m `mod` s == 0
    delem (CF f@(StepField _ _) _ _) _ _
      = error $ "delem(BCronField): Unimplemented " ++ show f

    -- dpred
    dpred (CF Star lo _) _ (Quant m)
      | lo<=(m-1) = justQuant (m-1)
      | otherwise = Nothing

    dpred (CF (SpecificField _) _ _) _ _ = Nothing

    dpred (CF (RangeField a _) lo _) _ (Quant m)
      | m-1 >= lo' = justQuant (m-1)
      | otherwise  = Nothing
      where
        lo' = max lo a

    dpred (CF (StepField Star s) lo _) _ (Quant m)
      | m'>= lo   = justQuant m'
      | otherwise = Nothing
      where m' = (m `modFloor` s) - s

    dpred (CF (StepField (RangeField a _) s) lo _) _ (Quant m)
      | m'>= lo'   = justQuant m'
      | otherwise  = Nothing
      where m'  = (m `modFloor` s) - s
            lo' = max lo a

    dpred cf@(CF (ListField fs) lo hi) _ m = idpred f m
      where
        f = fromMaybe
            (error $ "dpred(ListField): no matches: " ++ show cf)
            (firstContaining fs lo hi (unQuant m))

    dpred (CF f@(StepField _ _) _ _) _ _
      = error $ "dpred(CronField): Unimplemented " ++ show f


    -- succ
    dsucc (CF Star _ hi) _ (Quant m)
      | hi>=(m+1) = justQuant (m+1)
      | otherwise = Nothing

    dsucc (CF (SpecificField _) _ _) _ _ = Nothing

    dsucc (CF (RangeField _ b) _ hi) _ (Quant m)
      | m+1 <= hi'  = justQuant (m+1)
      | otherwise   = Nothing
      where
        hi' = min hi b

    dsucc (CF (StepField Star s) _ hi) _ (Quant m)
      | m'<= hi   = justQuant m'
      | otherwise = Nothing
      where m' = (m `modCeil` s) + s

    dsucc (CF (StepField (RangeField _ b) s) _ hi) _ (Quant m)
      | m'<= hi'   = justQuant m'
      | otherwise  = Nothing
      where m'  = (m `modCeil` s) + s
            hi' = min hi b

    dsucc cf@(CF (ListField fs) lo hi) _ m = idsucc f m
      where
        f  = fromMaybe
             (error $ "dsucc(ListField): no matches: " ++ show cf)
             (firstContaining fs lo hi (unQuant m))

    dsucc (CF f@(StepField _ _) _ _) _ _
      = error $ "dsucc(CronField): Unimplemented " ++ show f
    
    -- dfloor
    dfloor (CF Star lo hi) _ m
      | m>=lo     = justQuant $ min hi m
      | otherwise = Nothing

    dfloor (CF (SpecificField i) lo hi) _ m
      | m >= max lo i = justQuant $ min hi i
      | otherwise     = Nothing

    dfloor (CF (RangeField a b) lo hi) _ m
      | m   >= lo' = justQuant $ min hi' m
      | otherwise  = Nothing
      where
        hi' = min hi b
        lo' = max lo a

    dfloor (CF (StepField Star s) lo hi) _ m
      | m'>= lo   = justQuant $ min hi m'
      | otherwise = Nothing
      where m' = m `modFloor` s

    dfloor (CF (StepField (RangeField a b) s) lo hi) _ m
      | m'>= lo'  = justQuant $ min hi' m'
      | otherwise = Nothing
      where m' = m `modFloor` s
            lo' = max lo a
            hi' = min hi b

    dfloor (CF (ListField fs') lo hi) _ m
      | isEl      = idfloor f m
      | otherwise = maxFloor
      where
        fs       = [CF f' lo hi | f'<-fs']
        isEls    = zip (map (\f' -> idelem f' m) fs) fs
        isEl     = any fst isEls
        f        = snd . head . dropWhile (not.fst) $ isEls
        floors   = map (\f' -> idfloor f' m) fs
        maxFloor = case catMaybes floors of
                     [] -> Nothing
                     ps -> Just . maximum .filter (<=Quant m) $ ps

    dfloor (CF f@(StepField _ _) _ _) _ _
      = error $ "dfloor(CronField): Unimplemented " ++ show f
    
    -- dceiling
    dceiling (CF Star lo hi) _ m
      | m<=hi     = justQuant $ max lo m
      | otherwise = Nothing

    dceiling (CF (SpecificField i) lo hi) _ m
      | m<=min hi i = justQuant $ max lo i
      | otherwise   = Nothing

    dceiling (CF (RangeField a b) lo hi) _ m
      | m<=hi'    = justQuant $ max lo' m
      | otherwise = Nothing
      where
        lo' = max lo a
        hi' = min hi b

    dceiling (CF (StepField Star s) lo hi) _ m
      | m'<=hi    = justQuant $ max lo m'
      | otherwise = Nothing
      where m' = m `modCeil` s

    dceiling (CF (StepField (RangeField a b) s) lo hi) _ m
      | m'<=hi'   = justQuant $ max lo' m'
      | otherwise = Nothing
      where m'  = m `modCeil` s
            lo' = max lo a
            hi' = min hi b

    dceiling (CF (ListField fs') lo hi) d m
      | isEl      = dceiling f d m
      | otherwise = minCeil
      where
        fs      = [CF f' lo hi | f'<-fs']
        isEls   = zip (map (\f' -> idelem f' m) fs) fs
        isEl    = any fst isEls
        f       = snd . head . dropWhile (not.fst) $ isEls
        ceils   = map (\f' -> idceiling f' m) fs
        minCeil = case catMaybes ceils of
                    [] -> Nothing
                    ps -> Just . minimum .filter (>=Quant m) $ ps

    dceiling (CF f@(StepField _ _) _ _) _ _
      = error $ "dceiling(CronField): Unimplemented " ++ show f

firstContaining :: [CronField]
                -> Int -> Int -> Int -> Maybe BCronField
firstContaining fs lo hi m
  = case dropWhile (not . \f -> idelem f m) [CF f lo hi | f<-fs] of
           (f':_) -> Just f'
           _      -> Nothing

instance BoundedDimension BCronField where
    dfirst (CF Star                           lo _ ) = constQuant lo
    dfirst (CF (SpecificField i)              lo _ ) = constQuant $ max lo i
    dfirst (CF (RangeField a _)               lo _ ) = constQuant $ max lo a
    dfirst (CF (ListField fs)                 lo hi)
      = const $ minimum $ map (\f -> dfirst (CF f lo hi) undefined) fs
    dfirst (CF (StepField Star s)             lo _ )
      = constQuant (lo `modCeil` s)
    dfirst (CF (StepField (RangeField a _) s) lo _ )
      = constQuant (lo' `modCeil` s)
      where lo' = max lo a
    dfirst (CF f@(StepField _ _)              _  _ )
      = const $ error $ "dfirst(CronField): Unimplemented " ++ show f

    dlast  (CF Star                           _  hi) = constQuant hi
    dlast  (CF (SpecificField i)              _  hi) = constQuant $ min hi i
    dlast  (CF (RangeField _ b)               _  hi) = constQuant $ min hi b
    dlast  (CF (ListField fs)                 lo hi)
      = const $ maximum $ map (\f -> dfirst (CF f lo hi) undefined) fs
    dlast  (CF (StepField Star s)             _  hi)
      = constQuant (hi `modFloor` s)
    dlast  (CF (StepField (RangeField _ b) s) _  hi)
      = constQuant (hi' `modFloor` s)
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
    type Dependent   MinuteSpec = HourSpec
    delem    (Minutes cs) _ = idelem     (CF cs 0 59)
    dpred    (Minutes cs) _ = idpred     (CF cs 0 59)
    dsucc    (Minutes cs) _ = idsucc     (CF cs 0 59)
    dfloor   (Minutes cs) _ = idfloor    (CF cs 0 59)
    dceiling (Minutes cs) _ = idceiling  (CF cs 0 59)

instance BoundedDimension MinuteSpec where
    dfirst (Minutes cs) _ = idfirst (CF cs 0 59)
    dlast  (Minutes cs) _ = idlast  (CF cs 0 59)

instance Dimension HourSpec where
    type DimensionIx HourSpec = Int
    type Dependent   HourSpec = DayOfMonthSpec
    delem    (Hours cs) _ = idelem     (CF cs 0 23)
    dpred    (Hours cs) _ = idpred     (CF cs 0 23)
    dsucc    (Hours cs) _ = idsucc     (CF cs 0 23)
    dfloor   (Hours cs) _ = idfloor    (CF cs 0 23)
    dceiling (Hours cs) _ = idceiling  (CF cs 0 23)

instance BoundedDimension HourSpec where
    dfirst (Hours cs) _ = idfirst (CF cs 0 23)
    dlast  (Hours cs) _ = idlast  (CF cs 0 23)

instance Dimension DayOfMonthSpec where
    type DimensionIx DayOfMonthSpec = Int
    type Dependent   DayOfMonthSpec = MonthSpec :> Years
    delem    (DaysOfMonth cs) (Quant (m:>y)) = idelem     (CF cs 1 dpm)
      where dpm = daysPerMonth y m
    dpred    (DaysOfMonth cs) (Quant (m:>y)) = idpred     (CF cs 1 dpm)
      where dpm = daysPerMonth y m
    dsucc    (DaysOfMonth cs) (Quant (m:>y)) = idsucc     (CF cs 1 dpm)
      where dpm = daysPerMonth y m
    dfloor   (DaysOfMonth cs) (Quant (m:>y)) = idfloor    (CF cs 1 dpm)
      where dpm = daysPerMonth y m
    dceiling (DaysOfMonth cs) (Quant (m:>y)) = idceiling  (CF cs 1 dpm)
      where dpm = daysPerMonth y m

instance BoundedDimension DayOfMonthSpec where
    dfirst (DaysOfMonth cs) (Quant (m:>y)) = idfirst (CF cs 1 dpm)
      where dpm = daysPerMonth y m
    dlast  (DaysOfMonth cs) (Quant (m:>y)) = idlast  (CF cs 1 dpm)
      where dpm = daysPerMonth y m

daysPerMonth :: Int -> Int -> Int
daysPerMonth yr mth
  | mth == 2, isLeapYear' yr      = 29
  | mth == 2                      = 28
  | mth `elem` [4,6,9,11]         = 30
  | otherwise                     = 31
  where isLeapYear' = isLeapYear . fromIntegral

instance Dimension MonthSpec where
    type DimensionIx MonthSpec = Int
    type Dependent   MonthSpec = Years
    delem    (Months cs) _ = idelem     (CF cs 1 12)
    dpred    (Months cs) _ = idpred     (CF cs 1 12)
    dsucc    (Months cs) _ = idsucc     (CF cs 1 12)
    dfloor   (Months cs) _ = idfloor    (CF cs 1 12)
    dceiling (Months cs) _ = idceiling  (CF cs 1 12)

instance BoundedDimension MonthSpec where
    dfirst (Months cs) _  = idfirst (CF cs  1 12)
    dlast  (Months cs) _  = idlast  (CF cs  1 12)

instance Dimension Years where
    type DimensionIx Years = Int
    type Dependent   Years = ()
    delem    _ _ _         = True
    dpred    _ _ (Quant i) = justQuant (i-1)
    dsucc    _ _ (Quant i) = justQuant (i+1)
    dfloor   _ _ a         = justQuant a
    dceiling _ _ a         = justQuant a

type TimeIx = DimensionIx CronScheduleDim
type CronScheduleDim = MinuteSpec
                    :> HourSpec
                    :> DayOfMonthSpec 
                    :> (MonthSpec :> Years)
data Years = Years deriving Show

ndimIxToTime :: Quantized TimeIx -> Quantized UTCTime
ndimIxToTime = fmap dimIxToTime

dimIxToTime :: TimeIx -> UTCTime
dimIxToTime (mins :> hours :> dom :> (month :> year))
  = UTCTime (fromGregorian (fromIntegral year) month dom)
            (fromIntegral $ (hours*60+mins) * 60)

ntimeToDimIx :: Quantized UTCTime -> Quantized TimeIx
ntimeToDimIx = fmap timeToDimIx

timeToDimIx :: UTCTime -> TimeIx
timeToDimIx UTCTime {utctDay = uDay, utctDayTime = uTime }
  = mn :> hr :> dom :> (mth :> fromIntegral yr)
  where (yr, mth, dom) = toGregorian uDay
        --(_, _, dow)    = toWeekDate uDay
        TimeOfDay { todHour = hr, todMin  = mn} = timeToTimeOfDay uTime

scheduleToDim :: CronSchedule -> CronScheduleDim
scheduleToDim CronSchedule{..}
    = minute :> hour :> dayOfMonth :> (month :> Years)
