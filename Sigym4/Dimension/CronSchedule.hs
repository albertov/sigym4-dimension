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
    type Dependent   CronSchedule = ()
    delem    s = return . idelem (scheduleToDim s) . timeToDimIx
    dpred    s = return . qadaptMaybeTime (idpred (scheduleToDim s))
    dsucc    s = return . qadaptMaybeTime (idsucc (scheduleToDim s))
    dfloor   s = return . adaptMaybeTime (idfloor (scheduleToDim s))
    dceiling s = return . adaptMaybeTime (idceiling (scheduleToDim s))

adaptMaybeTime f = fmap ndimIxToTime . f . timeToDimIx
qadaptMaybeTime f = fmap ndimIxToTime . f . qtimeToDimIx

data BCronField = CF CronField Int Int deriving Show

instance Dimension BCronField where
    type DimensionIx BCronField = Int
    type Dependent BCronField = ()

    -- delem
    delem (CF Star lo hi) m
      = return $ lo<=m && m<=hi
    delem (CF (SpecificField i) _ _) m
      = return $ m==i
    delem (CF (RangeField a b) lo hi) m
      = return $ max lo a <= m && min hi b >= m
    delem (CF (ListField fs) lo hi) m
      = return $ any (\f -> idelem (CF f lo hi) m) fs
    delem (CF (StepField Star s) lo hi) m
      = return $ lo<=m && m<=hi && m `mod` s == 0
    delem (CF (StepField (RangeField a b) s) lo hi) m
      = return $ max lo a <= m && min hi b >= m && m `mod` s == 0
    delem (CF f@(StepField _ _) _ _) _ 
      = error $ "delem(BCronField): Unimplemented " ++ show f

    -- dpred
    dpred (CF Star lo _) m
      | lo<=m'    = yieldQuant m'
      | otherwise = stopIteration
      where m' = unQ m - 1

    dpred (CF (SpecificField _) _ _) _ = stopIteration

    dpred (CF (RangeField a _) lo _) m
      | lo'<=m'    = yieldQuant m'
      | otherwise  = stopIteration
      where
        lo' = max lo a
        m'  = unQ m - 1

    dpred (CF (StepField Star s) lo _) m
      | m'>= lo   = yieldQuant m'
      | otherwise = stopIteration
      where m' = (unQ m `modFloor` s) - s

    dpred (CF (StepField (RangeField a _) s) lo _) m
      | m'>= lo'   = yieldQuant m'
      | otherwise  = stopIteration
      where m'  = (unQ m `modFloor` s) - s
            lo' = max lo a

    dpred (CF (ListField fs') lo hi) m = return maxPred
      where
        fs      = filter (`idelem` (unQ m)) [CF f' lo hi | f'<-fs']
        maxPred = case catMaybes $ map (`idpred` m) fs of
                    [] -> Nothing
                    ps -> Just . maximum $ ps

    dpred (CF f@(StepField _ _) _ _) _ 
      = error $ "dpred(CronField): Unimplemented " ++ show f


    -- succ
    dsucc (CF Star _ hi) m
      | m'<=hi    = yieldQuant m'
      | otherwise = stopIteration
      where m' = unQ m + 1

    dsucc (CF (SpecificField _) _ _) _ = stopIteration

    dsucc (CF (RangeField _ b) _ hi) m
      | m'<=hi'     = yieldQuant m'
      | otherwise   = stopIteration
      where m'  = unQ m + 1
            hi' = min hi b

    dsucc (CF (StepField Star s) _ hi) m
      | m'<= hi   = yieldQuant m'
      | otherwise = stopIteration
      where m' = (unQ m `modCeil` s) + s

    dsucc (CF (StepField (RangeField _ b) s) _ hi) m
      | m'<= hi'   = yieldQuant m'
      | otherwise  = stopIteration
      where m'  = (unQ m `modCeil` s) + s
            hi' = min hi b

    dsucc (CF (ListField fs') lo hi) m = return minSucc
      where
        fs      = filter (`idelem` (unQ m)) [CF f' lo hi | f'<-fs']
        minSucc = case catMaybes $ map (`idsucc` m) fs of
                    [] -> Nothing
                    ps -> Just . minimum $ ps

    dsucc (CF f@(StepField _ _) _ _) _ 
      = error $ "dsucc(CronField): Unimplemented " ++ show f
    
    -- dfloor
    dfloor (CF Star lo hi) m
      | m>=lo     = yieldQuant $ min hi m
      | otherwise = stopIteration

    dfloor (CF (SpecificField i) lo hi) m
      | m >= max lo i = yieldQuant $ min hi i
      | otherwise     = stopIteration

    dfloor (CF (RangeField a b) lo hi) m
      | m   >= lo' = yieldQuant $ min hi' m
      | otherwise  = stopIteration
      where
        hi' = min hi b
        lo' = max lo a

    dfloor (CF (StepField Star s) lo hi) m
      | m'>= lo   = yieldQuant $ min hi m'
      | otherwise = stopIteration
      where m' = m `modFloor` s

    dfloor (CF (StepField (RangeField a b) s) lo hi) m
      | m'>= lo'  = yieldQuant $ min hi' m'
      | otherwise = stopIteration
      where m'  = m `modFloor` s
            lo' = max lo a
            hi' = min hi b

    dfloor (CF (ListField fs') lo hi) m = maxFloor
      where
        fs       = [CF f' lo hi | f'<-fs']
        maxFloor = case catMaybes $ map (`idfloor` m) fs of
                    [] -> stopIteration
                    ps -> yieldQuant . maximum . filter (<= m) . map unQ $ ps

    dfloor (CF f@(StepField _ _) _ _) _ 
      = error $ "dfloor(CronField): Unimplemented " ++ show f
    
    -- dceiling
    dceiling (CF Star lo hi) m
      | m<=hi     = yieldQuant $ max lo m
      | otherwise = stopIteration

    dceiling (CF (SpecificField i) lo hi) m
      | m<=min hi i = yieldQuant $ max lo i
      | otherwise   = stopIteration

    dceiling (CF (RangeField a b) lo hi) m
      | m<=hi'    = yieldQuant $ max lo' m
      | otherwise = stopIteration
      where
        lo' = max lo a
        hi' = min hi b

    dceiling (CF (StepField Star s) lo hi) m
      | m'<=hi    = yieldQuant $ max lo m'
      | otherwise = stopIteration
      where m' = m `modCeil` s

    dceiling (CF (StepField (RangeField a b) s) lo hi) m
      | m'<=hi'   = yieldQuant $ max lo' m'
      | otherwise = stopIteration
      where m'  = m `modCeil` s
            lo' = max lo a
            hi' = min hi b

    dceiling (CF (ListField fs') lo hi) m = minCeil
      where
        fs      = [CF f' lo hi | f'<-fs']
        minCeil = case catMaybes $ map (`idceiling` m) fs of
                    [] -> stopIteration
                    ps -> yieldQuant . minimum . filter (>= m) . map unQ $ ps

    dceiling (CF f@(StepField _ _) _ _) _
      = error $ "dceiling(CronField): Unimplemented " ++ show f


instance BoundedDimension BCronField where
    dfirst (CF Star lo _ ) = quant lo
    dfirst (CF (SpecificField i) lo _) = quant $ max lo i
    dfirst (CF (RangeField a _) lo _) = quant $ max lo a
    dfirst (CF (ListField fs) lo hi)
      = return $ minimum $ map (\f -> idfirst (CF f lo hi)) fs
    dfirst (CF (StepField Star s) lo _)
      = quant (lo `modCeil` s)
    dfirst (CF (StepField (RangeField a _) s) lo _)
      = quant (max lo a `modCeil` s)
    dfirst (CF f@(StepField _ _) _ _)
      = error $ "dfirst(CronField): Unimplemented " ++ show f

    dlast (CF Star _ hi) = quant hi
    dlast (CF (SpecificField i) _ hi) = quant $ min hi i
    dlast (CF (RangeField _ b) _ hi) = quant $ min hi b
    dlast (CF (ListField fs) lo hi)
      = return $ maximum $ map (\f -> idfirst (CF f lo hi)) fs
    dlast (CF (StepField Star s) _ hi)
      = quant (hi `modFloor` s)
    dlast  (CF (StepField (RangeField _ b) s) _  hi)
      = quant (min hi b `modFloor` s)
    dlast  (CF f@(StepField _ _) _ _)
      = error $ "dlast(CronField): Unimplemented " ++ show f

modFloor, modCeil :: Integral a => a -> a -> a
modFloor a m = a - (a `mod` m)
modCeil  a m
  | md == 0   = a
  | otherwise = a + (m-md)
  where md = a `mod` m

instance Dimension DayOfMonthSpec where
    type DimensionIx DayOfMonthSpec = Int
    type Dependent   DayOfMonthSpec = BCronField :* Infinite Int
    delem    = withDynamicDom idelem
    dpred    = withDynamicDom idpred
    dsucc    = withDynamicDom idsucc
    dfloor   = withDynamicDom idfloor
    dceiling = withDynamicDom idceiling

withDynamicDom f (DaysOfMonth cs) i
  = getDep >>= \d ->
    let m:*y = unQ d
        dpm  = daysPerMonth y m
    in return $ f (CF cs 1 dpm) i

instance BoundedDimension DayOfMonthSpec where
    dfirst = withDynamicDom0 idfirst
    dlast  = withDynamicDom0 idlast

withDynamicDom0 f (DaysOfMonth cs)
  = getDep >>= \d ->
    let m:*y = unQ d
        dpm  = daysPerMonth y m
    in return $ f (CF cs 1 dpm)


daysPerMonth :: Int -> Int -> Int
daysPerMonth yr mth
  | mth == 2, isLeapYear' yr      = 29
  | mth == 2                      = 28
  | mth `elem` [4,6,9,11]         = 30
  | otherwise                     = 31
  where isLeapYear' = isLeapYear . fromIntegral

type TimeIx = DimensionIx CronScheduleDim
type CronScheduleDim = BCronField
                    :* BCronField
                    :* DayOfMonthSpec 
                    :~ (BCronField :* Infinite Int)

ndimIxToTime :: Quantized TimeIx -> Quantized UTCTime
ndimIxToTime = fmap dimIxToTime

dimIxToTime :: TimeIx -> UTCTime
dimIxToTime (mins :* hours :* dom :* (month :* year))
  = UTCTime (fromGregorian (fromIntegral year) month dom)
            (fromIntegral $ (hours*60+mins) * 60)

qtimeToDimIx :: Quantized UTCTime -> Quantized TimeIx
qtimeToDimIx = fmap timeToDimIx

timeToDimIx :: UTCTime -> TimeIx
timeToDimIx UTCTime {utctDay = uDay, utctDayTime = uTime }
  = mn :* hr :* dom :* (mth :* fromIntegral yr)
  where (yr, mth, dom) = toGregorian uDay
        --(_, _, dow)    = toWeekDate uDay
        TimeOfDay { todHour = hr, todMin  = mn} = timeToTimeOfDay uTime

scheduleToDim :: CronSchedule -> CronScheduleDim
scheduleToDim  cs = CF mins 0 59 :* CF hrs 0 23 :* doms :~ (CF mths 1 12 :* Inf)
  where CronSchedule { minute     = Minutes mins
                     , hour       = Hours hrs
                     , dayOfMonth = doms
                     , month      = Months mths} = cs
