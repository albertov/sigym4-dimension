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
>            , TypeFamilies
>            , TypeOperators
>            , FlexibleContexts
>            #-}
> 

TODO: Falta definir el interfaz del módulo.

> module Sigym4.Dimension.Types where

Nos quitamos lo antes posible la importación de las librerías que
utilizaremos.
 
> import Data.Typeable (Typeable)


Comenzamos definiendo las dos clases principales.

Dimension
---------

Una 'Dimension' es un conjunto ordenado, posiblemente infinito, de
índices de dimension asociados 'DimensionIx'.
Las funciones que expone permiten determinar si un elemento
pertenece al conjunto o encontrar los elementos pertenecientes mayores
o menores para poder enumerarlos a partir de cualquier punto y en
cualquier dirección.

> -- | A 'Dimension' is a possibly infinite ordered set of associated
> --   'DimensionIx's
> --  A finite dimension should also implement 'BoundedDimension' and
> -- return 'Nothing' from 'dpred', 'dfloor', 'dsucc' and 'dceiling' when
> -- the next element would be > maximum or < minimum
> class (Eq (DimensionIx d), Ord (DimensionIx d))
>   => Dimension d
>   where
>     -- | The associated type of the elements
>     type DimensionIx d
>
>     -- | Whether or not an element belongs to the set
>     delem :: DimensionIx d -> d -> Bool
>
>     -- | 'Just' the succesive element of the set. Since a
>     --   'Dimension' can be of inifinite size it may
>     --   never return 'Nothing'
>     dsucc    :: d -> DimensionIx d -> Maybe (DimensionIx d)
>
>     -- | Returns 'Just' the previous element of the set. Since a
>     --   'Dimension' can be of inifinite size it should
>     --   never return 'Nothing'
>     dpred    :: d -> DimensionIx d -> Maybe (DimensionIx d)
>
>     -- | Clamps a 'DimensionIx' d which may not belong to
>     --   the set to the closest value which is <= d, 
>     --   'd' itself if it already belongs to the set.
>     dfloor   :: d -> DimensionIx d -> Maybe (DimensionIx d)
>
>     -- | Clamps a 'DimensionIx' d which possibly doesn't belong to
>     --   the set to the closest value which is >= d, possibly
>     --   'd' itself if it already belongs to the set.
>     dceiling :: d -> DimensionIx d -> Maybe (DimensionIx d)
>
>     {-# MINIMAL delem, dsucc, dpred, dfloor, dceiling #-}
>
>     -- | Similar to 'enumFrom' from 'Enum'
>     --   A default implementation is provided in terms of 'dsucc' and 'dfloor'
>     --   but instances may override to provide a more efficient implementation
>     denumUp :: d -> DimensionIx d -> [DimensionIx d]
>     denumUp d a = go (dfloor d a)
>       where go Nothing  = []
>             go (Just i) = i : go (dsucc d i)
>
>     -- | Similar to 'enumFrom' from 'Enum' but in reverse order
>     --   A default implementation is provided in terms of 'dpred' and
>     --   'dceiling' but instances may override to provide a more efficient
>     --   implementation
>     denumDown :: d -> DimensionIx d -> [DimensionIx d]
>     denumDown d a = go (dceiling d a)
>       where go Nothing  = []
>             go (Just i) = i : go (dpred d i)
                


BoundedDimension
----------------

Una 'BoundedDimension' es una 'Dimension' estrictamente finita con cotas
inferior y superior, ambas cerradas.

> -- | A 'BoundedDimension' is a finite 'Dimension'
> --   The implementation of 'dsucc', 'dpred', 'dceiling' and 'dfloor' from
> --   'Dimension a' must return 'Nothing' when out of bounds
> class Dimension d => BoundedDimension d where
>     dfirst   :: d -> DimensionIx d
>     dlast    :: d -> DimensionIx d
>
>     {-# MINIMAL dfirst, dlast #-}


Comenzamos definiendo algunas instancias de Dimensiones típicas, la primera
es la dimensión nula o escalar que sólo tiene un elemento. Se utilizará para
indexar datos estáticos.

> instance Dimension () where
>     type DimensionIx () = ()
>     delem () ()  = True
>     dpred    _ _ = Nothing
>     dsucc    _ _ = Nothing
>     dfloor   _ _ = Just ()
>     dceiling _ _ = Just ()
> 
> instance BoundedDimension () where
>     dfirst   _   = ()
>     dlast    _   = ()
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
>       = case a `compare` a' of
>           EQ -> b `compare` b'
>           o  -> o

Finalmete definimos cualquier producto de dimensiones como una dimensión.
Notese que es necesario que la "cola" de dimensiones no sea infinita aunque
la cabeza (y sólo la cabeza) puede serlo. Ésto es así porque si no sería
imposible determinar cuando se ha terminado de iterar las dimensiones interiores
para pasar a las exteriores.

Esta invariante la garantiza el sistema de tipos requiriendo `BoundedDimension`
en la variable de tipo `a`. Lo que no evita es una instancia mal implementada.

> instance (BoundedDimension a, Dimension b) => Dimension (a :> b) where
>     type DimensionIx (a :> b) = DimensionIx a :> DimensionIx b
> 
>     delem (a :> b) (da :> db) = a `delem` da && b `delem` db
> 
>     dpred (da :> db) (a :> b)
>       = case dpred da a of
>           Just a' -> Just (a' :> b)
>           Nothing -> case dpred db b of
>                        Nothing -> Nothing
>                        Just b' -> Just (dlast da :> b')
> 
>     dfloor (da :> db) (a :> b)
>       = case dfloor da a of
>           Just a' -> Just (a' :> b)
>           Nothing -> case dfloor db b of
>                        Nothing -> Nothing
>                        Just b' -> Just (dlast da :> b')
> 
>     dsucc (da :> db) (a :> b)
>       = case dsucc da a of
>           Just a' -> Just (a' :> b)
>           Nothing -> case dsucc db b of
>                        Nothing -> Nothing
>                        Just b' -> Just (dfirst da :> b')
> 
>     dceiling (da :> db) (a :> b)
>       = case dceiling da a of
>           Just a' -> Just (a' :> b)
>           Nothing -> case dceiling db b of
>                        Nothing -> Nothing
>                        Just b' -> Just (dfirst da :> b')

> instance (BoundedDimension a, BoundedDimension b) => BoundedDimension (a :> b) where
>     dfirst (a :> b) = dfirst a :> dfirst b
>     dlast  (a :> b) = dlast a  :> dlast b
