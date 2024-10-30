{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskellQuotes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Sigym4.Dimension.CronSchedule
  ( CronSchedule,
    cron,
    mkCronSchedule,
  )
where

import Control.Monad
import Data.Attoparsec.Text (endOfInput, parseOnly)
import Data.Foldable (toList)
import Data.String (IsString (fromString))
import Data.Text (Text)
import Data.Time.Calendar (fromGregorian, isLeapYear, toGregorian)
import Data.Time.Calendar.WeekDate (toWeekDate)
import Data.Time.Clock (UTCTime (..))
import Data.Time.LocalTime (TimeOfDay (..), timeToTimeOfDay)
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Sigym4.Dimension.Types
import System.Cron

instance Dimension CronSchedule where
  type DimensionIx CronSchedule = UTCTime
  type Dependent CronSchedule = ()
  delem s = return . idelem (scheduleToDim s) . timeToDimIx
  dpred s = return . qadaptMaybeTime (idpred (scheduleToDim s))
  dsucc s = return . qadaptMaybeTime (idsucc (scheduleToDim s))
  dfloor s = return . adaptMaybeTime (idfloor (scheduleToDim s))
  dceiling s = return . adaptMaybeTime (idceiling (scheduleToDim s))

adaptMaybeTime ::
  (TimeIx -> Maybe (Quantized TimeIx)) ->
  UTCTime ->
  Maybe (Quantized UTCTime)
adaptMaybeTime f = fmap ndimIxToTime . f . timeToDimIx

qadaptMaybeTime ::
  (Quantized TimeIx -> Maybe (Quantized TimeIx)) ->
  Quantized UTCTime ->
  Maybe (Quantized UTCTime)
qadaptMaybeTime f = fmap ndimIxToTime . f . qtimeToDimIx

data BCronField = CF CronField Int Int deriving (Show)

toCFs :: BCronField -> [BCronField]
toCFs (CF (ListField fs) lo hi) = toList $ fmap (\f -> CF (Field f) lo hi) fs
toCFs _ = error "toCFs is only defined for CF (ListField)"

instance Dimension BCronField where
  type DimensionIx BCronField = Int
  type Dependent BCronField = ()

  -- delem
  delem (CF (Field Star) lo hi) m = return $ lo <= m && m <= hi
  delem (CF (Field (SpecificField' (SpecificField i))) lo hi) m = return $ inInt lo hi m && m == i
  delem (CF (Field (RangeField' (RangeField a b))) lo hi) m = return $ inInt (max lo a) (min hi b) m
  delem f@(CF (ListField _) _ _) m = withDep (toCFs f `delem` m)
  delem (CF (StepField' (StepField Star s)) lo hi) m =
    return $ inInt lo hi m && m `mod` s == 0
  delem (CF (StepField' (StepField (RangeField' (RangeField a b)) s)) lo hi) m =
    return $ inInt (max lo a) (min hi b) m && m `mod` s == 0
  delem (CF (StepField' (StepField (SpecificField' (SpecificField x)) s)) lo hi) m =
    return $ inInt lo hi m && m `mod` s == x

  -- dpred
  dpred (CF (Field Star) lo _) m
    | lo <= m' = yieldQuant m'
    | otherwise = stopIteration
    where
      m' = unQ m - 1
  dpred (CF (Field (SpecificField' _)) _ _) _ = stopIteration
  dpred (CF (Field (RangeField' (RangeField a b))) lo hi) m
    | inInt lo' hi' m' = yieldQuant m'
    | otherwise = stopIteration
    where
      lo' = max lo a
      hi' = min hi b
      m' = unQ m - 1
  dpred (CF (StepField' (StepField Star s)) lo hi) m =
    yieldHead . dropWhile (>= unQ m) . reverse $ expand lo hi s
  dpred (CF (StepField' (StepField (RangeField' (RangeField a b)) s)) lo hi) m =
    yieldHead . dropWhile (>= unQ m) . reverse $
      expand
        (max lo a)
        (min hi b)
        s
  dpred f@(CF (ListField _) _ _) m = withDep (toCFs f `dpred` m)
  dpred (CF (StepField' (StepField (SpecificField' (SpecificField x)) s)) lo hi) m =
    yieldHead . dropWhile (>= unQ m) . reverse $ expandN x lo hi s

  -- succ
  dsucc (CF (Field Star) lo hi) m
    | inInt lo hi m' = yieldQuant m'
    | otherwise = stopIteration
    where
      m' = unQ m + 1
  dsucc (CF (Field (SpecificField' _)) _ _) _ = stopIteration
  dsucc (CF (Field (RangeField' (RangeField a b))) lo hi) m
    | inInt lo' hi' m' = yieldQuant m'
    | otherwise = stopIteration
    where
      m' = unQ m + 1
      hi' = min hi b
      lo' = max lo a
  dsucc (CF (StepField' (StepField Star s)) lo hi) m =
    yieldHead . dropWhile (<= unQ m) $ expand lo hi s
  dsucc (CF (StepField' (StepField (RangeField' (RangeField a b)) s)) lo hi) m =
    yieldHead . dropWhile (<= unQ m) $ expand (max lo a) (min hi b) s
  dsucc f@(CF (ListField _) _ _) m = withDep (toCFs f `dsucc` m)
  dsucc (CF (StepField' (StepField (SpecificField' (SpecificField x)) s)) lo hi) m =
    yieldHead . dropWhile (<= unQ m) $ expandN x lo hi s

  -- dfloor
  dfloor (CF (Field Star) lo hi) m
    | m >= lo = yieldQuant $ min hi m
    | otherwise = stopIteration
  dfloor (CF (Field (SpecificField' (SpecificField i))) lo hi) m
    | i <= m, lo <= i, i <= hi = yieldQuant i
    | otherwise = stopIteration
  dfloor (CF (Field (RangeField' (RangeField a b))) lo hi) m
    | lo' <= m, lo' <= hi' = yieldQuant $ min hi' m
    | otherwise = stopIteration
    where
      lo' = max lo a
      hi' = min hi b
  dfloor (CF (StepField' (StepField Star s)) lo hi) m =
    yieldHead . dropWhile (> m) . reverse $ expand lo hi s
  dfloor (CF (StepField' (StepField (RangeField' (RangeField a b)) s)) lo hi) m =
    yieldHead . dropWhile (> m) . reverse $ expand (max lo a) (min hi b) s
  dfloor f@(CF (ListField _) _ _) m = withDep (toCFs f `dfloor` m)
  dfloor (CF (StepField' (StepField (SpecificField' (SpecificField x)) s)) lo hi) m =
    yieldHead . dropWhile (> m) . reverse $ expandN x lo hi s

  -- dceiling
  dceiling (CF (Field Star) lo hi) m
    | m <= hi = yieldQuant $ max lo m
    | otherwise = stopIteration
  dceiling (CF (Field (SpecificField' (SpecificField i))) lo hi) m
    | m <= i, lo <= i, i <= hi = yieldQuant i
    | otherwise = stopIteration
  dceiling (CF (Field (RangeField' (RangeField a b))) lo hi) m
    | m <= hi', lo' <= hi' = yieldQuant $ max lo' m
    | otherwise = stopIteration
    where
      hi' = min hi b
      lo' = max lo a
  dceiling (CF (StepField' (StepField Star s)) lo hi) m =
    yieldHead . dropWhile (< m) $ expand lo hi s
  dceiling (CF (StepField' (StepField (RangeField' (RangeField a b)) s)) lo hi) m =
    yieldHead . dropWhile (< m) $ expand (max lo a) (min hi b) s
  dceiling f@(CF (ListField _) _ _) m = withDep (toCFs f `dceiling` m)
  dceiling (CF (StepField' (StepField (SpecificField' (SpecificField x)) s)) lo hi) m =
    yieldHead . dropWhile (< m) $ expandN x lo hi s

expand :: Integral t => t -> t -> t -> [t]
expand = expandN 0
{-# INLINE expand #-}

expandN :: Integral t => t -> t -> t -> t -> [t]
expandN n lo hi s = [i | i <- [lo .. hi], i `mod` s == n]
{-# INLINE expandN #-}

instance BoundedDimension BCronField where
  dfirst (CF (Field Star) lo _) = yieldQuant lo
  dfirst (CF (Field (SpecificField' (SpecificField i))) lo hi)
    | lo <= i, i <= hi = yieldQuant i
    | otherwise = stopIteration
  dfirst (CF (Field (RangeField' (RangeField a b))) lo hi)
    | lo' <= hi' = yieldQuant lo'
    | otherwise = stopIteration
    where
      lo' = max lo a
      hi' = min hi b
  dfirst f@(CF (ListField _) _ _) = withDep $ dfirst $ toCFs f
  dfirst (CF (StepField' (StepField Star s)) lo hi) =
    case expand lo hi s of
      [] -> stopIteration
      (x : _) -> yieldQuant x
  dfirst (CF (StepField' (StepField (RangeField' (RangeField a b)) s)) lo hi) =
    yieldHead $ expand (max lo a) (min hi b) s
  dfirst (CF (StepField' (StepField (SpecificField' (SpecificField x)) s)) lo hi) =
    case expandN x lo hi s of
      [] -> stopIteration
      (a : _) -> yieldQuant a

  dlast (CF (Field Star) _ hi) = yieldQuant hi
  dlast (CF (Field (SpecificField' (SpecificField i))) lo hi)
    | lo <= i, i <= hi = yieldQuant i
    | otherwise = stopIteration
  dlast (CF (Field (RangeField' (RangeField a b))) lo hi)
    | lo' <= hi' = yieldQuant hi'
    | otherwise = stopIteration
    where
      lo' = max lo a
      hi' = min hi b
  dlast f@(CF (ListField _) _ _) = withDep $ dlast $ toCFs f
  dlast (CF (StepField' (StepField Star s)) lo hi) =
    yieldHead . reverse $ expand lo hi s
  dlast (CF (StepField' (StepField (RangeField' (RangeField a b)) s)) lo hi) =
    yieldHead . reverse $ expand (max lo a) (min hi b) s
  dlast (CF (StepField' (StepField (SpecificField' (SpecificField x)) s)) lo hi) =
    yieldHead . reverse $ expandN x lo hi s

data DayOfMonthDim = DomDim CronField CronField deriving (Show)

instance Dimension DayOfMonthDim where
  type DimensionIx DayOfMonthDim = Int
  type Dependent DayOfMonthDim = BCronField :* Infinite Int
  delem (DomDim doms dows) i =
    getDowDpm i >>= \(dow, dpm) ->
      return $
        idelem (CF doms 1 dpm) i
          && idelem (CF dows 1 7) dow

  dpred (DomDim doms dows) i = do
    (_, dpm) <- getDowDpm (unQ i)
    let cfDoms = CF doms 1 dpm
        cfDows = CF dows 1 7
        loop v =
          maybe
            stopIteration
            ( \j ->
                getDowDpm (unQ j) >>= \(dow, _) ->
                  if cfDows `idelem` dow
                    then return (Just j)
                    else loop j
            )
            (idpred cfDoms v)

    loop i

  dsucc (DomDim doms dows) i = do
    (_, dpm) <- getDowDpm (unQ i)
    let cfDoms = CF doms 1 dpm
        cfDows = CF dows 1 7
        loop v =
          maybe
            stopIteration
            ( \j ->
                getDowDpm (unQ j) >>= \(dow, _) ->
                  if cfDows `idelem` dow
                    then return (Just j)
                    else loop j
            )
            (idsucc cfDoms v)

    loop i

  dfloor (DomDim doms dows) i = do
    (_, dpm) <- getDowDpm i
    let cfDoms = CF doms 1 dpm
        cfDows = CF dows 1 7
        loop v =
          maybe
            stopIteration
            ( \j ->
                getDowDpm (unQ j) >>= \(dow, _) ->
                  if cfDows `idelem` dow
                    then return (Just j)
                    else loop $ unQ j - 1
            )
            (idfloor cfDoms v)

    loop i

  dceiling (DomDim doms dows) i = do
    (_, dpm) <- getDowDpm i
    let cfDoms = CF doms 1 dpm
        cfDows = CF dows 1 7
        loop v =
          maybe
            stopIteration
            ( \j ->
                getDowDpm (unQ j) >>= \(dow, _) ->
                  if cfDows `idelem` dow
                    then return (Just j)
                    else loop $ unQ j + 1
            )
            (idceiling cfDoms v)

    loop i

getDowDpm ::
  DimensionIx (Dependent d) ~ (Int :* Int) =>
  Int ->
  Dim d (Int, Int)
getDowDpm dom =
  getDep >>= \d ->
    let m :* y = unQ d
        dpm = daysPerMonth y m
        (_, _, dow) = toWeekDate $ fromGregorian (fromIntegral y) m dom
     in return (dow, dpm)

instance BoundedDimension DayOfMonthDim where
  dfirst = withDynamicDom idfirst idsucc
  dlast = withDynamicDom idlast idpred

withDynamicDom ::
  (DimensionIx (Dependent d) ~ (Int :* Int)) =>
  (BCronField -> Maybe (Quantized Int)) ->
  (BCronField -> Quantized Int -> Maybe (Quantized Int)) ->
  DayOfMonthDim ->
  Dim d (Maybe (Quantized Int))
withDynamicDom f g (DomDim doms dows) =
  getDep >>= \d ->
    let m :* y = unQ d
        dpm = daysPerMonth y m
        cfDoms = CF doms 1 dpm
        cfDows = CF dows 1 7
        wDay day = dow
          where
            (_, _, dow) = toWeekDate $ fromGregorian (fromIntegral y) m day'
            day' = unQ day
        tryWith t = case t of
          Just j | cfDows `idelem` wDay j -> Just j
          Just j -> tryWith (g cfDoms j)
          _ -> Nothing
     in return $ tryWith (f cfDoms)

daysPerMonth :: Int -> Int -> Int
daysPerMonth yr mth
  | mth == 2, isLeapYear' yr = 29
  | mth == 2 = 28
  | mth `elem` [4, 6, 9, 11] = 30
  | otherwise = 31
  where
    isLeapYear' = isLeapYear . fromIntegral

data TruncatedSeconds = TruncatedSeconds

instance Dimension TruncatedSeconds where
  type DimensionIx TruncatedSeconds = Int
  type Dependent TruncatedSeconds = ()

  delem _ i = return (i == 0)
  dpred _ _ = stopIteration
  dsucc _ _ = stopIteration
  dfloor _ 0 = yieldQuant 0
  dfloor _ _ = stopIteration
  dceiling _ 0 = yieldQuant 0
  dceiling _ _ = stopIteration

instance BoundedDimension TruncatedSeconds where
  dfirst = const (yieldQuant 0)
  dlast = const (yieldQuant 0)

type TimeIx = DimensionIx CronScheduleDim

type CronScheduleDim =
  TruncatedSeconds
    :* BCronField
    :* BCronField
    :* DayOfMonthDim
    :~ (BCronField :* Infinite Int)

ndimIxToTime :: Quantized TimeIx -> Quantized UTCTime
ndimIxToTime = fmap dimIxToTime

dimIxToTime :: TimeIx -> UTCTime
dimIxToTime (secs :* mins :* hours :* dom :* (month :* year)) =
  UTCTime
    (fromGregorian (fromIntegral year) month dom)
    (fromIntegral (hours * 3600 + mins * 60 + secs))

qtimeToDimIx :: Quantized UTCTime -> Quantized TimeIx
qtimeToDimIx = fmap timeToDimIx

timeToDimIx :: UTCTime -> TimeIx
timeToDimIx UTCTime {utctDay = uDay, utctDayTime = uTime} =
  round secs :* mn :* hr :* dom :* (mth :* fromIntegral yr)
  where
    (yr, mth, dom) = toGregorian uDay
    TimeOfDay {todHour = hr, todMin = mn, todSec = secs} = timeToTimeOfDay uTime

scheduleToDim :: CronSchedule -> CronScheduleDim
scheduleToDim cs = TruncatedSeconds :* CF mins 0 59 :* CF hrs 0 23 :* domd :~ (CF mths 1 12 :* Inf)
  where
    CronSchedule
      { minute = Minutes mins,
        hour = Hours hrs,
        dayOfMonth = DaysOfMonth doms,
        dayOfWeek = DaysOfWeek dows,
        month = Months mths
      } = cs
    domd = DomDim doms dows

inInt :: Ord a => a -> a -> a -> Bool
inInt lo hi v = lo <= v && v <= hi

yieldHead :: [a] -> Dim d (Maybe (Quantized a))
yieldHead xs = case xs of
  [] -> stopIteration
  (c : _) -> yieldQuant c

mkCronSchedule :: Text -> Either String CronSchedule
mkCronSchedule = parseOnly (cronSchedule <* endOfInput)

unsafeParseCS :: String -> CronSchedule
unsafeParseCS = either (error "invalid CS") id . mkCronSchedule . fromString

cron :: QuasiQuoter
cron =
  QuasiQuoter
    { quoteExp = \s -> do
        void $ either fail return (parseOnly cronSchedule (fromString s))
        return (TH.VarE 'unsafeParseCS `TH.AppE` TH.LitE (TH.StringL s)),
      quotePat = const (fail "Cannot apply cron quasiquoter in patterns"),
      quoteType = const (fail "Cannot apply cron quasiquoter in types"),
      quoteDec = const (fail "Cannot apply cron quasiquoter in declarations")
    }
