Tiempos
-------

> {-# LANGUAGE GADTs
>            , GeneralizedNewtypeDeriving
>            , StandaloneDeriving
>            , DeriveDataTypeable
>            , TypeFamilies
>            , TypeSynonymInstances
>            , FlexibleInstances
>            #-}
> 

> module Sigym4.Dimension.Time (
>     Time(..)
>   , ForecastTime
>   , ObservationTime
>   , RunTime
>   , Horizon (..)
>   , minutes
>   , Horizons
>   , DynHorizons
>   , Schedule (..)
> ) where

> import Data.String (IsString(fromString))
> import Data.Time.Clock (UTCTime(..), NominalDiffTime, addUTCTime)
> import Data.Time ()
> import Data.Typeable (Typeable)
> import qualified Data.Set as S
> import GHC.Exts (IsList (..))
> import Sigym4.Dimension.Types
> import Sigym4.Dimension.CronSchedule

Preparamos el terreno para definir las dimensiones temporales creando tipos
para los distintos tipos de tiempo, todos son envoltorios de 'UTCTime'

 
ObservationTime es el tiempo asociado a una observación.

> newtype ObservationTime = ObsTime UTCTime
>   deriving (Eq, Ord, Show, Typeable)

RunTime es el tiempo asociado a cuando se realizó una pasada de un proceso
predictivo.

> newtype RunTime = RunTime UTCTime
>   deriving (Eq, Ord, Show, Typeable)

ForecastTime es el tiempo asociado a una prediccón hecha por un sistema
predictivo, es decir, la hora a la cual se predice una situación.

> newtype ForecastTime = FcTime UTCTime
>   deriving (Eq, Ord, Show, Typeable)


Para poder tener código agnostico al tipo de tiempo (pero sin perder la
información de tipado) definimos una clase 'Time' con operaciones
polimórificas.
 
> class (Show t, Eq t, Ord t) => Time t where
>     fromUTCTime :: UTCTime -> t
>     toUTCTime   :: t ->  UTCTime
>     addHorizon  :: Horizon -> t -> t
>     {-# MINIMAL fromUTCTime, toUTCTime, addHorizon #-}

Hacemos los tipos de tiempo miembros de la clase 'Time' de manera
simétrica para cada tipo.

Notese que el tiempo se trunca al minuto más cercano limitando la resolución
temporal efectiva del sistema a 1 minuto. Esta limitación se debe a que
la implementación de `Schedule` que no genera intervalos más finos.
En Sigym3 no ha dado problemas tener resolución de minuto, de hecho, la más fina
es cincominutal. 

> instance Time ObservationTime where
>     fromUTCTime = ObsTime . floorToMinute
>     toUTCTime (ObsTime t)  = t
>     addHorizon d (ObsTime t) = ObsTime (addUTCTime (toNominalDiffTime d) t)
> 
> instance Time ForecastTime where
>     fromUTCTime = FcTime . floorToMinute
>     toUTCTime (FcTime t)  = t
>     addHorizon d (FcTime t) = FcTime (addUTCTime (toNominalDiffTime d) t)
> 
> instance Time RunTime where
>     fromUTCTime = RunTime . floorToMinute
>     toUTCTime (RunTime t)  = t
>     addHorizon d (RunTime t) = RunTime (addUTCTime (toNominalDiffTime d) t)
> 
> floorToMinute :: UTCTime -> UTCTime
> floorToMinute (UTCTime d t) = UTCTime d t'
>     where t' = fromIntegral $ tr - (tr `mod` 60)
>           tr = round t :: Int
> 

Periodicidad
------------

Definimos un tipo para poder definir índices temporales periódicos.
 
> newtype Schedule t = Schedule CronSchedule deriving (Eq, Show, Typeable)

 
Lo hacemos de la clase `IsString` para poder escribir constantes como
cadenas de texto en formato de "cron". Ojo, dará error en ejecución
una cadena en formato incorrecto. Se puede arreglar con Template Haskell
parseando la cadena durante la compilación.

> instance IsString (Schedule t) where
>     fromString = Schedule . fromString

Definimos una instancia de 'Dimension' para 'Schedule's de
cualquier tipo de tiempo. Ojo, es bastante ineficiente aunque en Sigym3 no es
de lo que más duele. Se podría mejorar inspeccionando el `CronSchedule` y
adaptando el delta en 'denumFromTo' una vez se encuentra un punto válido.

> instance Time t => Dimension (Schedule t) where
>     type DimensionIx (Schedule t) = t
>     type Dependent   (Schedule t) = ()
>     delem    (Schedule s) = return . idelem s . toUTCTime
>     dpred    (Schedule s) = return . qadaptMaybeTime (idpred s)
>     dsucc    (Schedule s) = return . qadaptMaybeTime (idsucc s)
>     dfloor   (Schedule s) = return . adaptMaybeTime  (idfloor s)
>     dceiling (Schedule s) = return . adaptMaybeTime  (idceiling s)

> qfromUTCTime :: Time t => Quantized UTCTime -> Quantized t
> qfromUTCTime = fmap fromUTCTime

> qtoUTCTime :: Time t => Quantized t -> Quantized UTCTime
> qtoUTCTime = fmap toUTCTime

> adaptMaybeTime :: (Time t, Time a)
>   => (UTCTime -> Maybe (Quantized UTCTime))
>   -> a
>   -> Maybe (Quantized t)
> adaptMaybeTime f = fmap qfromUTCTime . f . toUTCTime

> qadaptMaybeTime :: (Time t1, Time t)
>   => (Quantized UTCTime -> Maybe (Quantized UTCTime))
>   -> Quantized t1
>   -> Maybe (Quantized t)
> qadaptMaybeTime f = fmap qfromUTCTime . f . qtoUTCTime

Horizontes
----------

Definimos un horizonte de predicción que representa un delta de tiempo en
distintas unidades interoperables.

También un alias para el tipo de los minutos para poder cambiarlo facilmente a
`Integer` si algún día hay horizontes larguísismos que desbordan el `Int`.
Es un 10% más rápido ejecutar los tests con `-a 500` al usar `Int`

> type Minutes = Int
> data Horizon = Minute !Minutes
>              | Hour   !Int
>              | Day    !Int
>   deriving (Show, Read, Typeable)

Definimos los minutos que contiene cada tipo de horizonte para poder normalizar
y operar con ellos.

> minutes :: Horizon -> Minutes
> minutes (Day d)    = fromIntegral d * 60 * 24
> minutes (Hour h)   = fromIntegral h * 60
> minutes (Minute m) = m

Definimos instancias para poder comparar horizontes.
 
> instance Eq Horizon where
>     Minute a == Minute b = a         == b
>     Hour a   == Hour b   = a         == b
>     Day a    == Day b    = a         == b
>     a        == b        = minutes a == minutes b
> 
> instance Ord Horizon where
>     Minute a `compare` Minute b = a         `compare` b
>     Hour a   `compare` Hour b   = a         `compare` b
>     Day a    `compare` Day b    = a         `compare` b
>     a        `compare` b        = minutes a `compare` minutes b

Definimos instancia de 'Num' para los horizontes para poder operar
como ellos como si fuesen números y para poder escribir constantes como números.

> instance Num Horizon where
>     Minute a + Minute b = Minute (a         + b        )
>     Hour a   + Hour b   = Hour   (a         + b        )
>     Day a    + Day b    = Day    (a         + b        )
>     a        + b        = Minute (minutes a + minutes b)
> 
>     Minute a * Minute b = Minute (a         * b        )
>     Hour a   * Hour b   = Hour   (a         * b        )
>     Day a    * Day b    = Day    (a         * b        )
>     a        * b        = Minute (minutes a * minutes b)
> 
>     Minute a - Minute b = Minute (a         - b        )
>     Hour a   - Hour b   = Hour   (a         - b        )
>     Day a    - Day b    = Day    (a         - b        )
>     a        - b        = Minute (minutes a - minutes b)
> 
>     negate (Minute a)   = Minute (negate a)
>     negate (Hour   a)   = Hour   (negate a)
>     negate (Day    a)   = Day    (negate a)
> 
>     abs    (Minute a)   = Minute (abs    a)
>     abs    (Hour   a)   = Hour   (abs    a)
>     abs    (Day    a)   = Day    (abs    a)
> 
>     signum (Minute a)   = Minute (signum a)
>     signum (Hour   a)   = Hour   (signum a)
>     signum (Day    a)   = Day    (signum a)
> 
>     fromInteger         = Minute . fromInteger

> toNominalDiffTime :: Horizon -> NominalDiffTime
> toNominalDiffTime = fromIntegral . (* 60) . minutes

Horizontes fijos
-----------------

Definimos un `newtype` para una lista de horizontes sin exportar su constructor.
Ésto lo hacemos para controlar su construcción en `fromList` la cual verifica
que no es una lista vacía para que el resto del código lo pueda asumir con
seguridad.

Encapsularlo con un `newtype` también permite poder cambiar la implementación
sin afectar al código que lo use, por ejemplo, si se da el caso de conjuntos
de muchos horizontes se puede cambiar la lista por un árbol binario que es
O(log n) en vez de O(n) en `dpred`, `dsucc`, `dfloor` y `dceiling`.

> type Horizons = S.Set Horizon

Definimos una instancia de `IsList` para poder escribir constantes como listas
habilitando la extension `XOverloadedLists`. Ojo, dará error en tiempo de
ejecución una lista vacía, también se puede arreglar con TemplateHaskell.

> instance IsList Horizons where
>     type Item Horizons  = Horizon
>     fromList l
>         | null l    = error "fromList(Horizons): Cannot be an empty list"
>         | otherwise = S.fromList l
>     toList  = S.toAscList
 
Horizontes dinámicos
--------------------

Definimos cualquier función de `RunTime` a lista de `Horizon`tes como una
dimensión dependiente. La utilizamos para los horizontes que dependen de la
fecha y hora de la pasada.

Ojo, ¡Es muy importante que la función devuelva siempre los horizontes ordenados
ascendentemente!

> type DynHorizons = RunTime -> [Horizon]
>
> instance Show DynHorizons where
>     show _ = "DynHorizons"
>
> instance Dimension DynHorizons where
>     type DimensionIx DynHorizons = Horizon
>     type Dependent   DynHorizons = Schedule RunTime
>     delem f d = getHs (elem d . f)
>     dpred f d = getHs f >>= \ds ->
>         case dropWhile (>= unQ d) (reverse ds) of
>           []    -> stopIteration
>           (x:_) -> yieldQuant x
>     dsucc f d = getHs f >>= \ds ->
>         case dropWhile (<= unQ d) ds of
>           []    -> stopIteration
>           (x:_) -> yieldQuant x
>     dfloor f d = getHs f >>= \ds ->
>         case dropWhile (> d) (reverse ds) of
>           []    -> stopIteration
>           (x:_) -> yieldQuant x
>     dceiling f d = getHs f >>= \ds ->
>         case dropWhile (< d) ds of
>           []    -> stopIteration
>           (x:_) -> yieldQuant x
> 
> instance BoundedDimension DynHorizons where
>     dfirst f = getHs f >>= \ds -> if null ds then stopIteration
>                                              else yieldQuant $ head ds
>     dlast f  = getHs f >>= \ds -> if null ds then stopIteration
>                                              else yieldQuant $ last ds
>
> getHs :: (DimensionIx (Dependent d) -> b) -> Dim d b
> getHs f = getDep >>= return . f . unQ
