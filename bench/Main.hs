{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

import Criterion.Main
import Control.DeepSeq

import Sigym4.Dimension

main :: IO ()
main = do
  defaultMain [
      benchSched [cron|* * * * *|]
    , benchSched [cron|0 0 * * *|]
    , benchSched [cron|0 */6 * * *|]
    , benchSched [cron|0 0,6,12,18 * * *|]
    , benchSched [cron|0 0 29 2 *|]
    , benchSched [cron|0 0 29 2 1|]
    ]

benchSched :: CronSchedule -> Benchmark
benchSched sched 
  = bench ("schedule: "  ++ show sched) (whnf force (take n $ idenumUp sched t))
  where t = datetime 2014 3 1 0 0
        n = 10000
