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

Se define el interfaz del módulo y se importan las librerías necesarias.

> module Sigym4.Dimension.Types (
>     Dimension(..)
>   , BoundedDimension(..)
>   , (:>)(..)
> ) where
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
>     type Dependent d
>     dfirst   :: d -> Dependent d -> DimensionIx d
>     dlast    :: d -> Dependent d -> DimensionIx d
>     {-# MINIMAL dfirst, dlast #-}
>     denum    :: d -> Dependent d -> [DimensionIx d]
>     denum d d2 = denumUp d (dfirst d d2)


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
>     type Dependent () = ()
>     dfirst _ _  = ()
>     dlast  _ _  = ()
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


> instance (BoundedDimension a, Dimension b, DimensionIx b ~ Dependent a)
>   => Dimension (a :> b) where
>     type DimensionIx (a :> b) = DimensionIx a :> DimensionIx b
> 
>     delem (a :> b) (da :> db) = a `delem` da && b `delem` db
> 
>     dpred (da :> db) (a :> b)
>       | b `delem` db
>       = case dpred da a of
>           Just a' | a'>=dfirst da b
>                   -> Just (a' :> b)
>           _       -> case dpred db b of
>                        Nothing -> Nothing
>                        Just b' -> Just (dlast da b' :> b')
>       | otherwise  = dfloor db b >>= \b' -> dpred (da :> db) (a :> b')
> 
>     dsucc (da :> db) (a :> b)
>       | b `delem` db
>       = case dsucc da a of
>           Just a' | a'<=dlast da b
>                   -> Just (a' :> b)
>           _       -> case dsucc db b of
>                        Nothing -> Nothing
>                        Just b' -> Just (dfirst da b' :> b')
>       | otherwise  = dceiling db b >>= \b' -> dsucc (da :> db) (a :> b')
> 
>     dfloor (da :> db) (a :> b)
>       | b `delem` db
>       = case dfloor da a of
>           Just a' | a'>=dfirst da b
>                   -> dfloor db b >>= \b' -> Just (a' :> b')
>           _       -> dpred  db b >>= \b' -> Just (dlast da b' :> b')
>       | otherwise  = dfloor db b >>= \b' -> Just (dlast da b' :> b')
> 
>     dceiling (da :> db) (a :> b)
>       | b `delem` db
>       = case dceiling da a of
>           Just a' | a'<=dlast da b
>                   -> dceiling db b >>= \b' -> Just (a' :> b')
>           _       -> dsucc    db b >>= \b' -> Just (dfirst da b' :> b')
>       | otherwise  = dceiling db b >>= \b' -> Just (dfirst da b' :> b')

El producto de dos `BoundedDimension` es a su vez una `BoundedDimension`

> instance (BoundedDimension a, BoundedDimension b, Dependent a ~ DimensionIx b)
>   => BoundedDimension (a :> b)
>   where
>     type Dependent (a :> b) = Dependent b
>     dfirst (a :> b) c = let fb = dfirst b c in dfirst a fb :> fb
>     dlast  (a :> b) c = let lb = dlast  b c in dlast  a lb :> lb
