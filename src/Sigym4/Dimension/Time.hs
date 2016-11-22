{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Sigym4.Dimension.Time (
    ForecastTime    (..)
  , ObservationTime (..)
  , RunTime         (..)
  , Observation
  , Prediction
  , PredictionDyn
  , Horizon (..)
  , minutes
  , Horizons (..)
  , DynHorizons
  , Interval
  , interval
  , boundedInterval
  , intq
  , intrtq
  , parseInterval
  , iterateDuration
  , module Data.Time
  , module Data.Time.ISO8601.Duration
  , Newtype
) where

import           Sigym4.Dimension.Types

import           Control.Applicative
import           Control.Newtype
import           Data.Attoparsec.ByteString (Parser)
import           Data.Attoparsec.ByteString.Char8 as AP hiding (takeWhile)
import           Data.Proxy
import qualified Data.ByteString.Char8 as BS
import           Data.Coerce (Coercible, coerce)
import           Data.Time
import           Data.Time.ISO8601.Duration
import qualified Data.Time.ISO8601.Interval as I
import           Debug.Trace

import Data.Typeable (Typeable)
import qualified Data.Set as S
-- #if !MIN_VERSION_containers(0,5,6)
import GHC.Exts (IsList (..))
-- #endif
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
-- 
-- Preparamos el terreno para definir las dimensiones temporales creando tipos
-- para los distintos tipos de tiempo, todos son envoltorios de 'UTCTime'
-- 
--  
-- ObservationTime es el tiempo asociado a una observación.
-- 
--
newtype ObservationTime = ObservationTime { getObservationTime :: UTCTime }
  deriving (Eq, Ord, Show, Typeable)

instance Newtype ObservationTime UTCTime where
  pack = ObservationTime
  unpack = getObservationTime

-- 
-- RunTime es el tiempo asociado a cuando se realizó una pasada de un proceso
-- predictivo.
-- 
newtype RunTime = RunTime { getRunTime :: UTCTime }
  deriving (Eq, Ord, Show, Typeable)

instance Newtype RunTime UTCTime where
  pack = RunTime
  unpack = getRunTime

-- 
-- ForecastTime es el tiempo asociado a una prediccón hecha por un sistema
-- predictivo, es decir, la hora a la cual se predice una situación.
-- 
newtype ForecastTime = ForecastTime { getForecastTime :: UTCTime }
  deriving (Eq, Ord, Show, Typeable)

instance Newtype ForecastTime UTCTime where
  pack = ForecastTime
  unpack = getForecastTime


truncateToSecond :: Newtype t UTCTime => t -> t
truncateToSecond (unpack -> UTCTime d t) =
  pack (UTCTime d (fromIntegral (truncate t :: Int)))

-- 
-- Periodicidad
-- ------------
-- 
-- Definimos un tipo para poder definir índices temporales periódicos.
-- NB: No usamos Data.Time.ISO8601.Interval porque puede representar estados
-- que no tienen sentido (eg: JustDuration) o no podemos calcular
-- eficientemente (eg: DurationEnd)
--  
data Interval t
  = StartDuration    t   Duration
  | StartEndDuration t t Duration
  deriving (Eq, Show, Typeable)

intervalStart :: Interval t -> t
intervalStart (StartDuration    s   _) = s
intervalStart (StartEndDuration s _ _) = s

intervalEnd :: Interval t -> Maybe t
intervalEnd (StartDuration    _   _) = Nothing
intervalEnd (StartEndDuration _ e _) = Just e

interval :: Newtype t UTCTime => Duration -> t -> Either String (Interval t)
interval d = Right . flip StartDuration d . truncateToSecond

boundedInterval
  :: (Ord t, Newtype t UTCTime)
  => Duration -> t -> t -> Either String (Interval t)
boundedInterval _ s e | s>e = Left "Start time is greater than end time"
boundedInterval d s e | not (belongsToInterval d s e e) =
  Left "End time is not a multiple of the period"
boundedInterval d s e =
  Right (StartEndDuration (truncateToSecond s) (truncateToSecond e) d)

belongsToInterval :: (Newtype a UTCTime, Ord a) => Duration -> a -> a -> a -> Bool
belongsToInterval d s e =
  (`elemMonotonic` (takeWhile (<=e) $ iterateDuration d s)) . truncateToSecond

-- Definimos una instancia de 'Dimension' para 'Interval's de
-- cualquier tipo de tiempo. Ojo, es bastante ineficiente aunque en Sigym3 no es
-- de lo que más duele. Se podría mejorar inspeccionando el `Duration` y
-- adaptando el delta en 'denumFromTo' una vez se encuentra un punto válido.
-- 
instance (Show t, Ord t, Newtype t UTCTime) => Dimension (Interval t) where
  type DimensionIx (Interval t) = t
  type Dependent   (Interval t) = ()

  --delem d t | traceShow ("delem", d, t) False = undefined
  delem (StartDuration    _   d) _ | isNullDuration d = return False
  delem (StartDuration    s   d) t = return . (`elemMonotonic` iterateDuration d s)
                                   . truncateToSecond $ t

  delem (StartEndDuration _ _ d) _ | isNullDuration d = return False
  delem (StartEndDuration s e d) t = return . belongsToInterval d s e $ t


  dsucc (StartDuration    _   d) | isNullDuration d = const stopIteration
  dsucc (StartDuration    _   d) = yieldQuant . pack . addDuration d . unpack . unQ

  dsucc (StartEndDuration _ _ d) | isNullDuration d = const stopIteration
  dsucc (StartEndDuration _ e d) = \t ->
    let next = pack ((addDuration d) (unpack (unQ t)))
    in if next > e then stopIteration else yieldQuant next
                                      

  --dpred d t | traceShow ("dpred", d, unQ t) False = undefined
  dpred (StartDuration    _   d) _ | isNullDuration d = stopIteration
  dpred (StartDuration    s   _) t | unQ t <= s       = stopIteration
  -- FIXME: This one is quite inefficient!
  dpred (StartDuration    s   d) t =
    yieldQuant (last (takeWhile (< unQ t) (iterateDuration d s)))

  dpred (StartEndDuration    _ _ d) _ | isNullDuration d = stopIteration
  dpred (StartEndDuration    s _ _) t | unQ t <=  s      = stopIteration
  dpred (StartEndDuration    _ e _) t | unQ t > e        = yieldQuant e
  -- FIXME: This one is quite inefficient!
  dpred (StartEndDuration    s _ d) t =
    yieldQuant (last (takeWhile (< unQ t) (iterateDuration d s)))


  dfloor (StartDuration    s   _) t | t < s            = stopIteration
  dfloor (StartDuration    s   _) t | t == s           = yieldQuant s
  dfloor (StartDuration    _   d) _ | isNullDuration d = stopIteration
  --dfloor d t | traceShow ("dfloor", d, t) False = undefined
  -- FIXME: This one is quite inefficient!
  dfloor (StartDuration    s   d) t =
    yieldQuant (last (takeWhile (<= t) (iterateDuration d s)))

  dfloor (StartEndDuration    s _ _) t | t < s            = stopIteration
  dfloor (StartEndDuration    s _ _) t | t == s           = yieldQuant s
  dfloor (StartEndDuration    _ e _) t | t > e            = yieldQuant e
  dfloor (StartEndDuration    _ _ d) _ | isNullDuration d = stopIteration
  --dfloor d t | traceShow ("dfloor", d, t) False = undefined
  -- FIXME: This one is quite inefficient!
  dfloor (StartEndDuration    s _ d) t =
    yieldQuant (last (takeWhile (<= t) (iterateDuration d s)))


  dceiling (StartDuration    _ d) _ | isNullDuration d = stopIteration
  dceiling (StartDuration    s _) t | t <= s           = yieldQuant s
  dceiling (StartDuration    s d) t =
    yieldQuant (head (dropWhile (< t) (iterateDuration d s)))

  dceiling (StartEndDuration _ _ d) _ | isNullDuration d = stopIteration
  dceiling (StartEndDuration s _ _) t | t < s            = yieldQuant s
  dceiling (StartEndDuration _ e _) t | t > e            = stopIteration
  dceiling (StartEndDuration _ e _) t | t == e           = yieldQuant e
  dceiling (StartEndDuration s e d) t = do
    next <- fmap unQ <$> dceiling (StartDuration s d) t
    maybe stopIteration (yieldQuant . min e) next

  denumUp (StartDuration    s   d') a =
    mapQuant . dropWhile (< a) $ iterateDuration d' s
  denumUp (StartEndDuration    _  e _ ) a | a>e = return []
  denumUp (StartEndDuration    s  e d') a =
    mapQuant . takeWhile (<=e) . dropWhile (< a) $ iterateDuration d' s
  -- FIXME: This one is quite inefficient!

  denumDown (StartDuration    s   _ ) a | a<s = return []
  denumDown (StartDuration    s   d') a =
    mapQuant . reverse . takeWhile (<= a) $ iterateDuration d' s
  denumDown (StartEndDuration    s e _ ) a | a<s = return []
  denumDown (StartEndDuration    s e d') a =
    mapQuant . reverse . takeWhile (<= min a e) $ iterateDuration d' s
  -- FIXME: This one is quite inefficient!

elemMonotonic :: Ord a => a -> [a] -> Bool
elemMonotonic a = go where
  go (x:_)  | x==a = True
  go (x:xs) | x<a  = go xs
  go (x:_)  | x>a  = False
  go _             = False

iterateDuration :: Newtype t UTCTime => Duration -> t -> [ t ]
iterateDuration d = iterate (pack . addDuration d . unpack)


isNullDuration :: Duration -> Bool
isNullDuration = (==t) . flip addDuration t
  where t = UTCTime (fromGregorian 0 1 1) 0
  -- FIXME: we can be more efficient here...

-- 
-- Horizontes
-- ----------
-- 
-- Definimos un horizonte de predicción que representa un delta de tiempo en
-- distintas unidades interoperables.
-- 
-- También un alias para el tipo de los minutos para poder cambiarlo facilmente a
-- `Integer` si algún día hay horizontes larguísismos que desbordan el `Int`.
-- Es un 10% más rápido ejecutar los tests con `-a 500` al usar `Int`
-- 
type Minutes = Int
data Horizon = Minute !Minutes
             | Hour   !Int
             | Day    !Int
  deriving (Show, Read, Typeable)
-- 
-- Definimos los minutos que contiene cada tipo de horizonte para poder normalizar
-- y operar con ellos.
-- 
minutes :: Horizon -> Minutes
minutes (Day d)    = fromIntegral d * 60 * 24
minutes (Hour h)   = fromIntegral h * 60
minutes (Minute m) = m
-- 
-- Definimos instancias para poder comparar horizontes.
--  
instance Eq Horizon where
    Minute a == Minute b = a         == b
    Hour a   == Hour b   = a         == b
    Day a    == Day b    = a         == b
    a        == b        = minutes a == minutes b

instance Ord Horizon where
    Minute a `compare` Minute b = a         `compare` b
    Hour a   `compare` Hour b   = a         `compare` b
    Day a    `compare` Day b    = a         `compare` b
    a        `compare` b        = minutes a `compare` minutes b
-- 
-- Definimos instancia de 'Num' para los horizontes para poder operar
-- como ellos como si fuesen números y para poder escribir constantes como números.
-- 
instance Num Horizon where
    Minute a + Minute b = Minute (a         + b        )
    Hour a   + Hour b   = Hour   (a         + b        )
    Day a    + Day b    = Day    (a         + b        )
    a        + b        = Minute (minutes a + minutes b)

    Minute a * Minute b = Minute (a         * b        )
    Hour a   * Hour b   = Hour   (a         * b        )
    Day a    * Day b    = Day    (a         * b        )
    a        * b        = Minute (minutes a * minutes b)

    Minute a - Minute b = Minute (a         - b        )
    Hour a   - Hour b   = Hour   (a         - b        )
    Day a    - Day b    = Day    (a         - b        )
    a        - b        = Minute (minutes a - minutes b)

    negate (Minute a)   = Minute (negate a)
    negate (Hour   a)   = Hour   (negate a)
    negate (Day    a)   = Day    (negate a)

    abs    (Minute a)   = Minute (abs    a)
    abs    (Hour   a)   = Hour   (abs    a)
    abs    (Day    a)   = Day    (abs    a)

    signum (Minute a)   = Minute (signum a)
    signum (Hour   a)   = Hour   (signum a)
    signum (Day    a)   = Day    (signum a)

    fromInteger         = Minute . fromInteger
-- 
toNominalDiffTime :: Horizon -> NominalDiffTime
toNominalDiffTime = fromIntegral . (* 60) . minutes
-- 
-- Horizontes fijos
-- -----------------
-- 
-- Definimos un `newtype` para una lista de horizontes sin exportar su constructor.
-- Ésto lo hacemos para controlar su construcción en `fromList` la cual verifica
-- que no es una lista vacía para que el resto del código lo pueda asumir con
-- seguridad.
-- 
-- Encapsularlo con un `newtype` también permite poder cambiar la implementación
-- sin afectar al código que lo use, por ejemplo, si se da el caso de conjuntos
-- de muchos horizontes se puede cambiar la lista por un árbol binario que es
-- O(log n) en vez de O(n) en `dpred`, `dsucc`, `dfloor` y `dceiling`.
-- 
newtype Horizons = Horizons { getHorizons :: S.Set Horizon }
  deriving (Eq, Show)


instance Dimension Horizons where
   type DimensionIx Horizons = Horizon
   type Dependent Horizons   = ()
   delem = overDim delem
   dsucc = overDim dsucc
   dpred = overDim dpred
   dfloor = overDim dfloor
   dceiling = overDim dceiling

instance BoundedDimension Horizons where
  dfirst = overDim_ dfirst
  dlast  = overDim_ dlast

instance Newtype Horizons (S.Set Horizon) where
  pack   = Horizons
  unpack = getHorizons

-- 
-- #if !MIN_VERSION_containers(0,5,6)
-- 
-- Definimos una instancia de `IsList` para poder escribir constantes como listas
-- habilitando la extension `XOverloadedLists`. Ojo, dará error en tiempo de
-- ejecución una lista vacía, también se puede arreglar con TemplateHaskell.
-- 
instance IsList Horizons where
    type Item Horizons  = Horizon
    fromList l
        | null l    = error "fromList(Horizons): Cannot be an empty list"
        | otherwise = Horizons (S.fromList l)
    toList  = S.toAscList . getHorizons
-- #endif
-- 
-- Horizontes dinámicos
-- --------------------
-- 
-- Definimos cualquier función de `RunTime` a lista de `Horizon`tes como una
-- dimensión dependiente. La utilizamos para los horizontes que dependen de la
-- fecha y hora de la pasada.
-- 
-- Ojo, ¡Es muy importante que la función devuelva siempre los horizontes ordenados
-- ascendentemente!
-- 
type DynHorizons = RunTime -> [Horizon]

instance Show DynHorizons where
    show _ = "DynHorizons"

instance Dimension DynHorizons where
    type DimensionIx DynHorizons = Horizon
    type Dependent   DynHorizons = Interval RunTime
    delem f d = getHs (elem d . f)
    dpred f d = getHs f >>= \ds ->
        case dropWhile (>= unQ d) (reverse ds) of
          []    -> stopIteration
          (x:_) -> yieldQuant x
    dsucc f d = getHs f >>= \ds ->
        case dropWhile (<= unQ d) ds of
          []    -> stopIteration
          (x:_) -> yieldQuant x
    dfloor f d = getHs f >>= \ds ->
        case dropWhile (> d) (reverse ds) of
          []    -> stopIteration
          (x:_) -> yieldQuant x
    dceiling f d = getHs f >>= \ds ->
        case dropWhile (< d) ds of
          []    -> stopIteration
          (x:_) -> yieldQuant x

instance BoundedDimension DynHorizons where
    dfirst f = getHs f >>= \ds -> if null ds then stopIteration
                                             else yieldQuant $ head ds
    dlast f  = getHs f >>= \ds -> if null ds then stopIteration
                                             else yieldQuant $ last ds

getHs :: (DimensionIx (Dependent d) -> b) -> Dim d b
getHs f = getDep >>= return . f . unQ
-- 
-- Definimos aliases de tipo de dimensiones compuestas comunes para no tener que
-- habilitar TypeOperators en los clientes.
-- 
type Observation = Interval ObservationTime
type Prediction = Horizons :* Interval RunTime
type PredictionDyn = DynHorizons :* Interval RunTime




unsafeParseInterval :: (Ord t, Newtype t UTCTime) => BS.ByteString -> Interval t
unsafeParseInterval =
  either (error . ("Could not parse Interval: "++)) id . parseInterval

parseInterval
  :: forall t. (Ord t, Newtype t UTCTime)
  => BS.ByteString -> Either String (Interval t)
parseInterval = parseOnly (interval' <* endOfInput) where
  interval' :: Newtype t UTCTime => Parser (Interval t)
  interval' = bounded <|> unbounded
  bounded, unbounded :: Parser (Interval t)
  bounded = do
    s <- pack <$> I.isoTime <* char '/'
    e <- pack <$> I.isoTime <* char '/'
    d <- duration
    either fail return (boundedInterval d s e)
  unbounded = do
    s <- pack <$> I.isoTime <* char '/'
    d <- duration
    either fail return (interval d s)

intrtq :: QuasiQuoter
intrtq = intq (Proxy :: Proxy RunTime)

intq :: forall t. (Ord t, Newtype t UTCTime) => Proxy t -> QuasiQuoter
intq _ = QuasiQuoter
  { quoteExp = \s -> do
      either fail (\(_::Interval t) -> return ()) (parseInterval (BS.pack s))
      return (TH.VarE 'unsafeParseInterval `TH.AppE` (TH.LitE (TH.StringL s)))
  , quotePat  = const (fail "Cannot apply interval quasiquoter in patterns")
  , quoteType = const (fail "Cannot apply interval quasiquoter in types")
  , quoteDec  = const (fail "Cannot apply interval quasiquoter in declarations")
  }