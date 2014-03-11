Dimensiones
===========

Este módulo implementa el concepto de dimensiones no-espaciales en Sigym4.
Éstas pueden ser temporales (observación, fecha de predicción, ..), de
horizonte de predicción ('Horizon') o nula.

A diferencia de Sigym3 se pueden definir nuevas dimensiones implementando
instancias de la clase 'Dimension'.

Hay dos tipos principales, las dimensiones (de clase 'Dimension a'), que
representan conjuntos ordenados, finitos ('BoundedDimension') o infinitos,
de índices de dimensión ('DimensionIx a'). Los productos de dimensiones
(en ciertos casos que se explicarán más adelante) también son
dimensiones por lo que se pueden definir sin demasiada burocracía nuevas
dimensiones que son producto de otras.

La implementación pretende evitar en la medida de lo posible errores en
ejecución (eg: indexar la dimensión del tiempo con una altura) por lo que
se utilizan familias de tipos para asociar el tipo de índice con cada
dimensión. Para ello necesitamos habilitar algunas extensiones de GHC
porque no se pueden expresar con Haskell2010.

> {-# LANGUAGE DeriveDataTypeable
>            , DeriveFunctor
>            , TypeFamilies
>            , TypeOperators
>            , FlexibleContexts
>            #-}
> 

Se define el interfaz del módulo y se importan las librerías necesarias.

> module Sigym4.Dimension.Types (
>     Dimension(..)
>   , BoundedDimension(..)
>   , Quantized (..)
>   , justQuant
>   , constQuant
>   , idelem
>   , idfloor
>   , idceiling
>   , idpred
>   , idsucc
>   , idenumDown
>   , idenumUp
>   , idfirst
>   , idlast
>   , idenum
>   , idenumr
>   , (:>)(..)
> ) where
> import Data.Typeable (Typeable)


Comenzamos definiendo las dos clases principales.

Dimension
---------

Una 'Dimension' es un conjunto ordenado, posiblemente infinito, de
índices discretos de dimension asociados 'DimensionIx'. Los índices que
pertenecen a una dimensión se dice que están "cuantizados" y se envuelven
con el tipo `Quantized` para señalarlo.

Las funciones que las instancias implementan permiten:

 * Preguntar si un elemento pertenece al conjunto mediante `delem`.
 * Encontrar el siguiente elemento cuantizado menor o igual a un elemento dado
   mediante `dfloor`.
 * Encontrar el siguiente elemento cuantizado mayor o igual a un elemento dado
   mediante `dceiling`.
 * Encontrar el siguiente elemento cuantizado menor a un elemento cuantizado
   dado mediante `dpred`.
 * Encontrar el siguiente elemento cuantizado mayor a un elemento cuantizado
   dado mediante `dsucc`.

Todas las instancias deben satisfacer 6 propiedades:

  1. ∀ dsucc    a ∊ dim, a ∊ dim, -> dsucc a > a
  2. ∀ dpred    a ∊ dim, a ∊ dim  -> dpred a < a
  3. ∀ dfloor   a ∊ dim, a        -> dfloor a <= a
  4. ∀ dceiling a ∊ dim, a        -> dceiling a >= a
  5. ∀ dfloor   a ∊ dim, dfloor b ∊ dim, dfloor c ∊ dim, a < b < c
     -> dfloor a <= dfloor b <= dfloor c
  6. ∀ dceiling   a ∊ dim, dceiling b ∊ dim, dceiling c ∊ dim, a > b > c
     -> dceiling a >= dceiling b >= dceiling c

Existe una especificación genérica válida para comprobarlas en cualquier
instancia de `Dimension` en los tests.


Definimos un envoltorio para etiquetar los valores que pertencecen a una
dimensión. Esta información extra de tipo intenta prevenir un mal uso del
API (eg: usar dsucc/dpred sobre elementos no cuantizados). Ojo, no impide
que un valor cuantizado a ∊ dimA se use en dimB donde dimA y dimB son del
mismo tipo de dimensión pero distintas (TODO: estudiar como prevenirlo con
los tipos sin introducir chequeos en ejecución)

> newtype Quantized a = Quant {unQuant::a}
>   deriving (Eq, Ord, Show, Functor, Typeable)

> justQuant :: a -> Maybe (Quantized a)
> justQuant = Just . Quant

> constQuant :: a -> b -> Quantized a
> constQuant = const . Quant

> type DDimensionIx d = Quantized (DimensionIx (Dependent d))

> -- | A 'Dimension' is a possibly infinite ordered set of associated
> --   'DimensionIx's
> --  A finite dimension should also implement 'BoundedDimension' and
> -- return 'Nothing' from 'dpred', 'dfloor', 'dsucc' and 'dceiling' when
> -- the next element would be > maximum or < minimum
> class (Show d, Show (DimensionIx d), Eq (DimensionIx d), Ord (DimensionIx d))
>   => Dimension d
>   where
>     -- | The associated type of the elements
>     type DimensionIx d

>     type Dependent d

>     -- | Whether or not an element belongs to the set
>     delem :: d
>           -> DDimensionIx d
>           -> DimensionIx d -> Bool

>     -- | 'Just' the succesive element of the set. Since a
>     --   'Dimension' can be of inifinite size it may
>     --   never return 'Nothing'
>     dsucc :: d
>           -> DDimensionIx d
>           -> Quantized (DimensionIx d)
>           -> Maybe (Quantized(DimensionIx d))

>     -- | Returns 'Just' the previous element of the set. Since a
>     --   'Dimension' can be of inifinite size it should
>     --   never return 'Nothing'
>     dpred :: d
>           -> DDimensionIx d
>           -> Quantized (DimensionIx d)
>           -> Maybe (Quantized(DimensionIx d))

>     -- | Clamps a 'DimensionIx' d which may not belong to
>     --   the set to the closest value which is <= d, 
>     --   'd' itself if it already belongs to the set.
>     dfloor :: d
>            -> DDimensionIx d
>            -> DimensionIx d -> Maybe (Quantized(DimensionIx d))

>     -- | Clamps a 'DimensionIx' d which possibly doesn't belong to
>     --   the set to the closest value which is >= d, possibly
>     --   'd' itself if it already belongs to the set.
>     dceiling :: d
>              -> DDimensionIx d
>              -> DimensionIx d -> Maybe (Quantized(DimensionIx d))

>     {-# MINIMAL delem, dsucc, dpred, dfloor, dceiling #-}

>     -- | Similar to 'enumFrom' from 'Enum'
>     --   A default implementation is provided in terms of 'dsucc' and 'dfloor'
>     --   but instances may override to provide a more efficient implementation
>     denumUp :: d
>             -> DDimensionIx d
>             -> DimensionIx d -> [Quantized(DimensionIx d)]
>     denumUp d dd a = go (dfloor d dd a)
>       where go Nothing  = []
>             go (Just i) = i : go (dsucc d dd i)

>     -- | Similar to 'enumFrom' from 'Enum' but in reverse order
>     --   A default implementation is provided in terms of 'dpred' and
>     --   'dceiling' but instances may override to provide a more efficient
>     --   implementation
>     denumDown :: d
>               -> DDimensionIx d
>               -> DimensionIx d -> [Quantized(DimensionIx d)]
>     denumDown d dd a = go (dceiling d dd a)
>       where go Nothing  = []
>             go (Just i) = i : go (dpred d dd i)


Definimos atajos para dimensiones independientes (de tipo Dependent ())

> qZ :: Quantized ()
> qZ = Quant ()

> idelem :: (Dimension d, DimensionIx (Dependent d) ~ ())
>   => d -> DimensionIx d -> Bool
> idelem d = delem d qZ

> idfloor, idceiling :: (Dimension d, DimensionIx (Dependent d) ~ ())
>   => d -> DimensionIx d -> Maybe (Quantized (DimensionIx d))
> idfloor d = dfloor d qZ
> idceiling d = dceiling d qZ

> idpred, idsucc :: (Dimension d, DimensionIx (Dependent d) ~ ())
>   => d -> Quantized (DimensionIx d) -> Maybe (Quantized (DimensionIx d))
> idpred d = dpred d qZ
> idsucc d = dsucc d qZ

> idenumUp, idenumDown :: (Dimension d, DimensionIx (Dependent d) ~ ())
>   => d -> DimensionIx d -> [Quantized (DimensionIx d)]
> idenumUp d = denumUp d qZ
> idenumDown d = denumDown d qZ

BoundedDimension
----------------

Una 'BoundedDimension' es una 'Dimension' estrictamente finita con cotas
inferior y superior, ambas cerradas.

> -- | A 'BoundedDimension' is a finite 'Dimension'
> --   The implementation of 'dsucc', 'dpred', 'dceiling' and 'dfloor' from
> --   'Dimension a' must return 'Nothing' when out of bounds
> class Dimension d => BoundedDimension d where
>     dfirst :: d -> DDimensionIx d -> Quantized (DimensionIx d)

>     dlast :: d -> DDimensionIx d -> Quantized (DimensionIx d)

>     {-# MINIMAL dfirst, dlast #-}

>     denum :: d -> DDimensionIx d -> [Quantized (DimensionIx d)]
>     denum d dd = denumUp d dd  $ unQuant $ dfirst d dd

>     denumr   :: d -> DDimensionIx d -> [Quantized (DimensionIx d)]
>     denumr d dd = denumDown d dd  $ unQuant $ dlast d dd


Definimos atajos para dimensiones acotadas independientes (de tipo Dependent ())

> idfirst, idlast :: (BoundedDimension d, DimensionIx (Dependent d) ~ ())
>                 => d -> Quantized (DimensionIx d)
> idfirst d = dfirst d qZ
> idlast d  = dlast d  qZ

> idenum, idenumr :: (BoundedDimension d, DimensionIx (Dependent d) ~ ())
>                 => d -> [Quantized (DimensionIx d)]
> idenum d  = denum d  qZ
> idenumr d = denumr d qZ

Comenzamos definiendo algunas instancias de Dimensiones típicas, la primera
es la dimensión nula o escalar que sólo tiene un elemento. Se utilizará para
indexar datos estáticos.

> instance Dimension () where
>     type DimensionIx () = ()
>     type Dependent   () = ()
>     delem    _ _ _ = True
>     dpred    _ _ _ = Nothing
>     dsucc    _ _ _ = Nothing
>     dfloor   _ _ _ = justQuant ()
>     dceiling _ _ _ = justQuant ()
> 
> instance BoundedDimension () where
>     dfirst _ _  = Quant ()
>     dlast  _ _  = Quant ()
> 


Dimensiones producto
--------------------

A continuación se prepara el terreno para definir dimensiones como
productos de otras, comenzando por un constructor para productos de
dimensiones y sus índices. La definición es similar a la de una tupla.
 
> infixl 3 :>
> data ts :> t
> 	= !ts :> !t
> 	deriving (Show, Eq, Read, Typeable)
> 

Éste producto es ordenable si sus elementos lo son.

> instance (Ord a, Ord b) => Ord (a :> b) where
>     (a :> b) `compare` (a' :> b')
>       = case b `compare` b' of
>           EQ -> a `compare` a'
>           o  -> o

Definimos cualquier producto de dimensiones como una dimensión.

Notese que es necesario que la "cola" de dimensiones
(ie: las dimensiones interiores) no sea infinita aunque la cabeza
(la dimensión exterior) sí puede serlo.  Esta invariante la garantiza el
sistema de tipos requiriendo `BoundedDimension` en la variable de tipo `a`.
Ésto es así porque si no sería imposible determinar cuando se ha terminado de
iterar las dimensiones interiores para pasar a la exterior.


> instance (BoundedDimension a, Dimension b, Dependent a ~ b)
>   => Dimension (a :> b) where
>     type DimensionIx (a :> b) = DimensionIx a :> DimensionIx b
>     type Dependent (a :> b)   = Dependent b
> 
>     delem (da :> db) c (a :> b) = delem da (Quant b) a && delem db c b
> 
>     dpred (da :> db) c (Quant (a :> b))
>       = case dpred da (Quant b) (Quant a) of
>           Just (Quant a')
>                   -> justQuant (a' :> b)
>           Nothing -> case dpred db c (Quant b) of
>                        Nothing         -> Nothing
>                        Just (Quant b') -> let Quant l = dlast da (Quant b')
>                                           in justQuant (l :> b')
> 
>     dsucc (da :> db) c (Quant (a :> b))
>       = case dsucc da (Quant b) (Quant a) of
>           Just (Quant a')
>                   -> justQuant (a' :> b)
>           Nothing -> case dsucc db c (Quant b) of
>                        Nothing         -> Nothing
>                        Just (Quant b') -> let Quant f = dfirst da (Quant b')
>                                           in justQuant (f :> b')
> 
>     dfloor (da :> db) c (a :> b)
>       | delem db c b
>       = let bq = Quant b
>         in case dfloor da bq a of
>           Just (Quant a')
>                   -> dfloor db c b  >>= \(Quant b') -> justQuant (a' :> b')
>           Nothing -> dpred  db c bq >>= \(Quant b') ->
>                                          let Quant l = dlast da (Quant b')
>                                          in justQuant (l :> b')
>       | otherwise  = dfloor db c b  >>= \(Quant b') ->
>                                          let Quant l = dlast da (Quant b')
>                                          in justQuant (l :> b')
> 
>     dceiling (da :> db) c (a :> b)
>       | delem db c b
>       = let bq = Quant b
>         in case dceiling da bq a of
>           Just (Quant a')
>                   -> dceiling db c b  >>= \(Quant b') -> justQuant (a' :> b')
>           Nothing -> dsucc    db c bq >>= \(Quant b') ->
>                                            let Quant f = dfirst da (Quant b')
>                                            in justQuant (f :> b')
>       | otherwise  = dceiling db c b  >>= \(Quant b') ->
>                                            let Quant f = dfirst da (Quant b')
>                                            in justQuant (f :> b')

El producto de dos `BoundedDimension` es a su vez una `BoundedDimension`

> instance (BoundedDimension a, BoundedDimension b, b ~ Dependent a)
>   => BoundedDimension (a :> b)
>   where
>     dfirst (a :> b) c = let Quant fb = dfirst b c
>                             Quant fa = dfirst a (Quant fb)
>                         in Quant (fa :> fb)
>     dlast  (a :> b) c = let Quant lb = dlast b c
>                             Quant la = dlast a (Quant lb)
>                         in Quant (la :> lb)
