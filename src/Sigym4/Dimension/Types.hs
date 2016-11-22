-- Dimensiones
-- ===========
-- 
-- Este módulo implementa el concepto de dimensiones no-espaciales en Sigym4.
-- Éstas pueden ser temporales (observación, fecha de predicción, ..), de
-- horizonte de predicción (`Horizon`) o nula.
-- 
-- A diferencia de Sigym3 se pueden definir nuevas dimensiones implementando
-- instancias de la clase `Dimension`.
-- 
-- Hay dos tipos principales, las dimensiones (de clase `Dimension a`), que
-- representan conjuntos ordenados, finitos ('BoundedDimension') o infinitos,
-- de índices de dimensión (`DimensionIx a`). Los productos de dimensiones
-- (en ciertos casos que se explicarán más adelante) también son
-- dimensiones por lo que se pueden definir sin demasiada burocracía nuevas
-- dimensiones que son producto de otras.
-- 
-- La implementación pretende evitar en la medida de lo posible errores en
-- ejecución (eg: indexar la dimensión del tiempo con una altura) por lo que
-- se utilizan familias de tipos para asociar el tipo de índice con cada
-- dimensión. Para ello necesitamos habilitar algunas extensiones de GHC
-- porque no se pueden expresar con Haskell2010.
-- 
{-# LANGUAGE GeneralizedNewtypeDeriving
           , DeriveDataTypeable
           , DeriveFunctor
           , TypeFamilies
           , TypeOperators
           , FlexibleContexts
           , FlexibleInstances
           , ScopedTypeVariables
           , BangPatterns
           , CPP
           , Trustworthy
           #-}

-- 
-- Se define el interfaz del módulo...
-- 
module Sigym4.Dimension.Types (
  -- | * Tipos
    Dimension(..)
  , BoundedDimension(..)
  , Infinite (Inf)
  , Quantized (unQ)
  -- | * Atajos
  , idelem
  , idfloor
  , idceiling
  , idpred
  , idsucc
  , idenumDown
  , idenumUp
  , idfirst
  , idlast
  , idenum
  , idenumr
  , (:~)(..)
  , (:*)(..)
  -- | * Utilidades para instancias de 'Dimension'
  , Dim
  , getDep
  , withDep
  , runDim
  , irunDim
  , quant
  , mapQuant
  , yieldQuant
  , stopIteration
  , overDim
  , overDim_
) where
-- 
-- ... y se importan las librerías necesarias:
-- 
import Control.Monad.Loops (unfoldrM, anyM)
import Control.Monad.Reader (Reader, runReader, ask)
-- #if !MIN_VERSION_base(4,8,0)
import Control.Applicative (Applicative)
-- #endif
import Control.DeepSeq (NFData)
import Control.Newtype
import Data.Typeable (Typeable)
import Data.Maybe (catMaybes, isJust, fromJust)
import qualified Data.Set as S
import Data.List (partition)
import Data.Coerce (Coercible, coerce)

-- 
-- Dimension
-- ---------
-- 
-- Una 'Dimension' es un conjunto ordenado, posiblemente infinito, de
-- índices discretos de dimension asociados 'DimensionIx'. Los índices que
-- pertenecen a una dimensión se dice que están "cuantizados" y se envuelven
-- con el tipo `Quantized` para señalarlo.
-- 
-- Las funciones que las instancias implementan permiten:
-- 
--  * Preguntar si un elemento pertenece al conjunto mediante `delem`.
--  * Encontrar el siguiente elemento cuantizado menor o igual a un elemento dado
--    mediante `dfloor`.
--  * Encontrar el siguiente elemento cuantizado mayor o igual a un elemento dado
--    mediante `dceiling`.
--  * Encontrar el siguiente elemento cuantizado menor a un elemento cuantizado
--    dado mediante `dpred`.
--  * Encontrar el siguiente elemento cuantizado mayor a un elemento cuantizado
--    dado mediante `dsucc`.
-- 
-- Todas las instancias deben satisfacer 8 propiedades para garantizar continuidad
-- y buena ordenación:
-- 
--   1. ∀ dsucc a ∊ dim, a ∊ dim, ⇒ dsucc a > a
--   2. ∀ dpred a ∊ dim, a ∊ dim  ⇒  dpred a < a
--   3. ∀ dfloor a ∊ dim, a       ⇒  dfloor a <= a
--   4. ∀ dceiling a ∊ dim, a     ⇒  dceiling a >= a
--   5. ∀ dfloor a ∊ dim, dfloor b ∊ dim, dfloor c ∊ dim, a < b < c
--      ⇒  dfloor a <= dfloor b <= dfloor c
--   6. ∀ dceiling a ∊ dim, dceiling b ∊ dim, dceiling c ∊ dim, a > b > c
--      ⇒  dceiling a >= dceiling b >= dceiling c
--   7. ∀ dpred a ∊ dim, dpred b ∊ dim, dpred c ∊ dim, a < b < c
--      ⇒  dpred a < dpred b < dpred c
--   8. ∀ dsucc a ∊ dim, dsucc b ∊ dim, dsucc c ∊ dim, a > b > c
--      ⇒  dsucc a > dsucc b > dsucc c
-- 
-- Existe una especificación genérica válida para comprobarlas en cualquier
-- instancia de `Dimension` en los tests.
-- 
-- 
-- Definimos un envoltorio para etiquetar los valores que pertencecen a una
-- dimensión. Esta información extra de tipo intenta prevenir un mal uso del
-- API (eg: usar dsucc/dpred sobre elementos no cuantizados). Ojo, no impide
-- que un valor cuantizado a ∊ dimA se use en dimB donde dimA y dimB son del
-- mismo tipo de dimensión pero distintas (TODO: estudiar como prevenirlo con
-- los tipos sin introducir chequeos en ejecución)
-- 
newtype Quantized a = Quant {unQ :: a}
  deriving (Eq, Ord, Show, Functor, NFData, Typeable)

-- 
-- Definimos un alias para referirnos al tipo de índice cuantizado de la
-- dimensión dependiente.
-- 
type DDimensionIx d = Quantized (DimensionIx (Dependent d))
-- 
-- 
-- Definimos una mónada lectora para envolver el índice de la dimensión dependiente
-- para no tener que pasarlo explicitamente como parámetro y evitar que los
-- clientes de la librería creen valores cuantizados fuera de las instancias
-- de `Dimension`
-- 
newtype Dim d a = Dim {unDim :: Reader (DDimensionIx d) a}
  deriving (Functor, Applicative, Monad)

hoistDim :: Coercible (DDimensionIx d) (DDimensionIx d') => Dim d a -> Dim d' a
hoistDim = coerce
{-# INLINE hoistDim #-}


overDim
  :: ( Coercible (DimensionIx (Dependent d)) (DimensionIx (Dependent d'))
     , Coercible d d'
     , Coercible a a'
     , Coercible b b'
     , Newtype d' d -- redundant constraint to propagate the fundep: d' -> d
     )
  => (d -> a -> Dim d b) -> (d' -> a' -> Dim d' b')
overDim f s = fmap coerce . coerce f s
{-# INLINE overDim #-}


overDim_
  :: (DimensionIx (Dependent d) ~ DimensionIx (Dependent d'), Newtype n t) =>
  (t -> Dim d a) -> n -> Dim d' a
overDim_ f s = hoistDim $ f (unpack s)
{-# INLINE overDim_ #-}

-- | Wraps a value in 'Maybe Quantized' and lifts it to the 'Dim' monad
--   Signals that there is a valid next value.
--   Used to implement 'Dimension' instances.
yieldQuant :: a -> Dim d (Maybe (Quantized a))
yieldQuant q = return . Just . Quant $ q
{-# INLINE yieldQuant #-}

-- | Wraps a Nothing in 'Maybe Quantized' and lifts it to the 'Dim' monad
--   Signals that there are no more valid values.
--   Used to implement 'Dimension' instances.
stopIteration :: Dim d (Maybe a)
stopIteration = return Nothing
{-# INLINE stopIteration #-}

-- | Wraps a value in 'Quantized' and lifts it to the 'Dim' monad
quant :: a -> Dim d (Quantized a)
quant = return . Quant
{-# INLINE quant #-}

-- | Wraps a list of values in 'Quantized' and lifts it to the 'Dim' monad
mapQuant :: [a] -> Dim d [Quantized a]
mapQuant = return . map Quant
{-# INLINE mapQuant #-}

-- | Asks for the 'DimensionIx' of the dependent 'Dimension' from the
--   environment
getDep :: Dim d (DDimensionIx d)
getDep = Dim ask

-- | Computes a 'Dim d a' value given the dependent dimension index
--   and extracts it from it's monadic wrapper.
runDim :: Dim d a -> DDimensionIx d -> a
runDim = runReader . unDim

-- | Same as 'runDim' but only for independent dimensions (ie: those that
--   declare '()' as their 'Dependent')
irunDim :: Dependent d ~ () => Dim d a -> a
irunDim d = runDim d qZ
-- 
qZ :: Quantized ()
qZ = Quant ()
-- 
-- Definimos la clase de tipos que pueden usarse como una dimensión.
-- 
-- | A 'Dimension' is a possibly infinite ordered set of associated
--   'DimensionIx's
--  A finite dimension should also implement 'BoundedDimension' and
-- return 'Nothing' from 'dpred', 'dfloor', 'dsucc' and 'dceiling' when
-- the next element would be > maximum or < minimum
class Ord (DimensionIx d) => Dimension d
  where
    -- | The associated type of the elements
    type DimensionIx d

    type Dependent d

    -- | Whether or not an element belongs to the set
    delem :: d -> DimensionIx d -> Dim d Bool
    -- | 'Just' the succesive element of the set. Since a
    --   'Dimension' can be of inifinite size it may
    --   never return 'Nothing'
    dsucc :: d
          -> Quantized (DimensionIx d)
          -> Dim d (Maybe (Quantized(DimensionIx d)))

    -- | Returns 'Just' the previous element of the set. Since a
    --   'Dimension' can be of inifinite size it should
    --   never return 'Nothing'
    dpred :: d
          -> Quantized (DimensionIx d)
          -> Dim d (Maybe (Quantized(DimensionIx d)))

    -- | Clamps a 'DimensionIx' d which may not belong to
    --   the set to the closest value which is <= d, 
    --   'd' itself if it already belongs to the set.
    dfloor :: d -> DimensionIx d -> Dim d (Maybe (Quantized(DimensionIx d)))

    -- | Clamps a 'DimensionIx' d which possibly doesn't belong to
    --   the set to the closest value which is >= d, possibly
    --   'd' itself if it already belongs to the set.
    dceiling :: d -> DimensionIx d -> Dim d (Maybe (Quantized(DimensionIx d)))
    {-# MINIMAL delem, dsucc, dpred, dfloor, dceiling #-}

    -- | Similar to 'enumFrom' from 'Enum'
    --   A default implementation is provided in terms of 'dsucc' and 'dfloor'
    --   but instances may override to provide a more efficient implementation
    denumUp :: d -> DimensionIx d -> Dim d [Quantized(DimensionIx d)]
    denumUp d a = dfloor d a >>= unfoldrM go
      where go Nothing  = stopIteration
            go (Just i) = fmap (\next -> Just (i,next)) (dsucc d i)

    -- | Similar to 'enumFrom' from 'Enum' but in reverse order
    --   A default implementation is provided in terms of 'dpred' and
    --   'dceiling' but instances may override to provide a more efficient
    --   implementation
    denumDown :: d -> DimensionIx d -> Dim d [Quantized(DimensionIx d)]
    denumDown d a = unfoldrM go =<< dceiling d a
      where go Nothing  = stopIteration
            go (Just i) = fmap (\next -> Just (i,next)) (dpred d i)
-- 
-- Definimos atajos para dimensiones independientes (de tipo Dependent ())
-- 
idelem :: (Dimension d, Dependent d ~ ())
  => d -> DimensionIx d -> Bool
idelem d = irunDim . delem d
-- 
idfloor, idceiling :: (Dimension d, Dependent d ~ ())
  => d -> DimensionIx d -> Maybe (Quantized (DimensionIx d))
idfloor d = irunDim . dfloor d
idceiling d = irunDim . dceiling d
-- 
idpred, idsucc :: (Dimension d, Dependent d ~ ())
  => d -> Quantized (DimensionIx d) -> Maybe (Quantized (DimensionIx d))
idpred d = irunDim . dpred d
idsucc d = irunDim . dsucc d
-- 
idenumUp, idenumDown :: (Dimension d, Dependent d ~ ())
                     => d -> DimensionIx d -> [Quantized (DimensionIx d)]
idenumUp d = irunDim . denumUp d 
idenumDown d = irunDim . denumDown d

-- 
-- BoundedDimension
-- ----------------
-- 
-- Una 'BoundedDimension' es una 'Dimension' estrictamente finita con cotas
-- inferior y superior, ambas cerradas.
-- 
-- | A 'BoundedDimension' is a finite 'Dimension'
--   The implementation of 'dsucc', 'dpred', 'dceiling' and 'dfloor' from
--   'Dimension a' must return 'Nothing' when out of bounds
class Dimension d => BoundedDimension d where
    dfirst :: d -> Dim d (Maybe ((Quantized (DimensionIx d))))
    dlast :: d -> Dim d (Maybe (Quantized (DimensionIx d)))
    {-# MINIMAL dfirst, dlast #-}

    denum :: d -> Dim d [Quantized (DimensionIx d)]
    denum d = dfirst d >>= maybe (return []) (denumUp d . unQ)

    denumr   :: d -> Dim d [Quantized (DimensionIx d)]
    denumr d = dlast d >>= maybe (return []) (denumDown d . unQ)
-- 
-- 
-- Definimos atajos para dimensiones acotadas independientes (de tipo Dependent ())
-- 
idfirst, idlast :: (BoundedDimension d, Dependent d ~ ())
                => d -> Maybe (Quantized (DimensionIx d))
idfirst = irunDim . dfirst
idlast = irunDim . dlast
-- 
idenum, idenumr :: (BoundedDimension d, Dependent d ~ ())
                => d -> [Quantized (DimensionIx d)]
idenum = irunDim . denum
idenumr = irunDim . denumr
-- 
-- Comenzamos definiendo algunas instancias de Dimensiones típicas, la primera
-- es la dimensión nula o escalar que sólo tiene un elemento. Se utilizará para
-- indexar datos estáticos.
-- 
instance Dimension () where
    type DimensionIx () = ()
    type Dependent   () = ()
    delem    _ _ = return True
    dpred    _ _ = stopIteration
    dsucc    _ _ = stopIteration
    dfloor   _ _ = yieldQuant ()
    dceiling _ _ = yieldQuant ()

instance BoundedDimension () where
    dfirst _ = yieldQuant ()
    dlast  _ = yieldQuant ()

-- 
-- También definimos una instancia para usar cualquier tipo numérico como
-- dimensión "infinita".
-- 
data Infinite a = Inf deriving (Show, Eq)

instance (Num a, Ord a, Bounded a) => Dimension (Infinite a) where
    type DimensionIx (Infinite a) = a
    type Dependent   (Infinite a) = ()

    delem    _ _         = return True
    dpred    _ (Quant i) = if i==minBound then stopIteration
                           else yieldQuant (i-1)
    dsucc    _ (Quant i) = if i==maxBound then stopIteration
                           else yieldQuant (i+1)
    dfloor   _ a         = yieldQuant a
    dceiling _ a         = yieldQuant a
-- 
-- Dimensiones producto
-- --------------------
-- 
-- A continuación se prepara el terreno para definir dimensiones como
-- productos de otras, comenzando por un constructor para productos de
-- dimensiones y sus índices. Hay dos maneras de combinar dimensiones en producto:
-- 
--  * Con el operador `:*`, por ejemplo `Horizons :* Schedule Runtime`, cuando
--    la dimensión de la izquierda es independiente.
-- 
--  * Con el operador `:~` cuando la dimensión de la izquierda depende de los
--    índices de la derecha.
-- 
-- Para combinar los índices de ambos tipos de dimensiones se utiliza el
-- operador `:*`
--  
infixl 3 :*
data ts :* t = !ts :* !t
  deriving (Show, Eq, Read, Typeable)
-- 
infixl 3 :~
data ts :~ t
        = !ts :~ !t
        deriving (Show, Eq, Read, Typeable)
-- 
-- Los productos son ordenables si sus elementos lo son. Esta instancia la
-- necesitamos para que los índices sean ordenables.
-- 
instance (Ord a, Ord b) => Ord (a :* b) where
    (a :* b) `compare` (a' :* b')
      = case b `compare` b' of
          EQ -> a `compare` a'
          o  -> o
-- 
-- Definimos cualquier producto de dimensiones como una dimensión.
-- 
-- Notese que es necesario que la "cola" de dimensiones
-- (ie: las dimensiones interiores) no sea infinita aunque la cabeza
-- (la dimensión exterior) sí puede serlo.  Esta invariante la garantiza el
-- sistema de tipos requiriendo `BoundedDimension` en la variable de tipo `a`.
-- Ésto es así porque si no sería imposible determinar cuando se ha terminado de
-- iterar las dimensiones interiores para pasar a la exterior.
-- 
maxTryIfNoBound :: Int
maxTryIfNoBound = 1000
-- 
instance (BoundedDimension a, Dimension b, Dependent a ~ b)
  => Dimension (a :~ b) where
    type DimensionIx (a :~ b) = DimensionIx a :* DimensionIx b
    type Dependent (a :~ b)   = Dependent b

    delem (da :~ db) (a :* b) = do
     eb <- withDep $ delem db b
     return $ if eb then runDim (delem da a) (Quant b) else False

    dpred (da :~ db) (Quant (a :* b)) = loop maxTryIfNoBound (Quant b)
      where
        loop n b'
          | n > 0 = maybe (withPred db b' (try (n-1)))
                     (\a' -> combine a' b')
                     (runDim (dpred da (Quant a)) b')
          | otherwise = stopIteration
        try n p = maybe (loop n p) (`combine` p) (runDim (dlast da) p)

    dsucc (da :~ db) (Quant (a :* b)) = loop maxTryIfNoBound (Quant b)
      where
        loop n b'
          | n > 0 = maybe (withSucc db b' (try (n-1)))
                     (\a' -> combine a' b')
                     (runDim (dsucc da (Quant a)) b')
          | otherwise = stopIteration
        try n p = maybe (loop n p) (`combine` p) (runDim (dfirst da) p)

    dfloor (da :~ db) (a :* b)
      = withDep (delem db b) >>= \isElemOfB ->
        if isElemOfB then let qb = Quant b in
          maybe (withDep (dpred db qb) >>= maybe stopIteration combineLst)
                (`combine` qb)
                (runDim (dfloor da a) qb)
        else withDep (dfloor db b) >>= maybe stopIteration combineLst
      where combineLst b' = findWith (dlast da) (dpred db) b'
                        >>= maybe stopIteration (uncurry combine)

    dceiling (da :~ db) (a :* b)
      = withDep (delem db b) >>= \isElemOfB ->
        if isElemOfB then let qb = Quant b in
          maybe (withDep (dsucc db qb) >>= maybe stopIteration combineFst)
                (`combine` qb)
                (runDim (dceiling da a) qb)
        else withDep (dceiling db b) >>= maybe stopIteration combineFst
      where combineFst b' = findWith (dfirst da) (dsucc db) b'
                        >>= maybe stopIteration (uncurry combine)
-- 
-- Las utilidades que acabamos de utilizar.
-- 
findWith :: (DimensionIx (Dependent d) ~ t3, DimensionIx (Dependent d2) ~ t3)
  => Dim d1 (Maybe t)
  -> (DDimensionIx d1 -> Dim d2 (Maybe (DDimensionIx d1)))
  -> DDimensionIx d1
  -> Dim d (Maybe (t, DDimensionIx d1))
findWith f g = loop maxTryIfNoBound
  where
    loop 0 _ = stopIteration
    loop n v | isJust (runDim f v) = return $ Just (fromJust (runDim f v), v)
             | otherwise  = withDep (g v) >>= maybe stopIteration (loop (n-1))
-- 
-- 
withDep :: (DimensionIx (Dependent d1) ~ t2, DimensionIx (Dependent d) ~ t2)
  => Dim d1 b -> Dim d b
withDep d = getDep >>= return . runDim d
-- 
-- 
withSucc, withPred ::
  ( Dimension d1, DimensionIx (Dependent d) ~ t2
  , DimensionIx (Dependent d1) ~ t2)
  => d1
  -> Quantized (DimensionIx d1)
  -> (Quantized (DimensionIx d1) -> Dim d (Maybe a))
  -> Dim d (Maybe a)
withSucc d v f = withDep (dsucc d v) >>= maybe stopIteration f
withPred d v f = withDep (dpred d v) >>= maybe stopIteration f
-- 
-- 
iyieldWithFirst, iyieldWithLast :: (BoundedDimension d1, Dependent d1 ~ ())
  => d1
  -> Quantized t
  -> Dim d (Maybe (Quantized (DimensionIx d1 :* t)))
iyieldWithFirst da b
  = maybe stopIteration (`combine` b) (irunDim (dfirst da))
iyieldWithLast da b
  = maybe stopIteration (`combine` b) (irunDim (dlast da))
-- 
-- 
combine :: Quantized ts -> Quantized t -> Dim d (Maybe (Quantized (ts :* t)))
combine a b = yieldQuant (unQ a :* unQ b)
-- 
-- 
-- Definimos de manera similar la instancia de `Dimension` para los productos
-- de dimension independiente y dimensión. La única diferencia es que no
-- pasamos el índice de la dimensión exterior a la interior (usando `irunDim`).
-- 
instance (BoundedDimension a, Dimension b, Dependent a ~ ())
  => Dimension (a :* b) where
    type DimensionIx (a :* b) = DimensionIx a :* DimensionIx b
    type Dependent (a :* b)   = Dependent b

    delem (da :* db) (a :* b) = do
     eb <- withDep $ delem db b
     return $ if eb then irunDim (delem da a) else False

    dpred (da :* db) (Quant (a :* b))
      = maybe (withPred db (Quant b) (iyieldWithLast da))
              (\a' -> yieldQuant (unQ a' :* b))
              (irunDim (dpred da (Quant a)))

    dsucc (da :* db) (Quant (a :* b))
      = maybe (withSucc db (Quant b) (iyieldWithFirst da))
              (\a' -> yieldQuant (unQ a' :* b))
              (irunDim (dsucc da (Quant a)))

    dfloor (da :* db) (a :* b)
      = withDep (delem db b) >>= \isElemOfB ->
        if isElemOfB then
          maybe (withPred db (Quant b) (iyieldWithLast da))
                (\a' -> yieldQuant (unQ a' :* b))
                (irunDim (dfloor da a))
        else withDep (dfloor db b)
         >>= maybe stopIteration (iyieldWithLast da)

    dceiling (da :* db) (a :* b)
      = withDep (delem db b) >>= \isElemOfB ->
        if isElemOfB then
          maybe (withSucc db (Quant b) (iyieldWithFirst da))
                (\a' -> yieldQuant (unQ a' :* b))
                (irunDim (dceiling da a))
        else withDep (dceiling db b)
         >>= maybe stopIteration (iyieldWithFirst da)
-- 
-- Los productos `:~` de dos `BoundedDimension` es a su vez una `BoundedDimension`
-- 
instance (BoundedDimension a, BoundedDimension b, b ~ Dependent a)
  => BoundedDimension (a :~ b)
  where
    dfirst (a :~ b) = do
      fb <- withDep (dfirst b)
      let fa = maybe Nothing (runDim (dfirst a)) fb
      case (fa,fb) of
        (Just fa', Just fb') -> combine fa' fb'
        _                    -> stopIteration

    dlast  (a :~ b) = do
      fb <- withDep (dlast b)
      let fa = maybe Nothing (runDim (dlast a)) fb
      case (fa,fb) of
        (Just fa', Just fb') -> combine fa' fb'
        _                    -> stopIteration
-- 
-- Los productos `:*` también.
-- 
instance (BoundedDimension a, BoundedDimension b, Dependent a ~ ())
  => BoundedDimension (a :* b)
  where
    dfirst (a :* b) = do
      fb <- withDep (dfirst b)
      let fa = irunDim (dfirst a)
      case (fa,fb) of
        (Just fa', Just fb') -> combine fa' fb'
        _                    -> stopIteration

    dlast  (a :* b) = do
      fb <- withDep (dlast b)
      let fa = irunDim (dlast a)
      case (fa,fb) of
        (Just fa', Just fb') -> combine fa' fb'
        _                    -> stopIteration

-- 
-- 
-- Conjuntos
-- ---------
-- 
-- Podermos definir trivialmente cualquier conjunto `Data.Set.Set` como una
-- `BoundedDimension`.
-- 
instance Ord a => Dimension (S.Set a) where
   type DimensionIx (S.Set a) = a
   type Dependent (S.Set a)   = ()
   delem s e    = return $ S.member e s
   dsucc s e    = return . fmap Quant $ S.lookupGT (unQ e) s
   dpred s e    = return . fmap Quant $ S.lookupLT (unQ e) s
   dfloor s e   = return . fmap Quant $ S.lookupLE e s
   dceiling s e = return . fmap Quant $ S.lookupGE e s
-- 
instance Ord a => BoundedDimension (S.Set a) where
   dfirst s | S.null s  = stopIteration
            | otherwise = yieldQuant . S.findMin $ s
   dlast  s | S.null s  = stopIteration
            | otherwise = yieldQuant . S.findMax $ s
   denum  = return . map Quant . S.toAscList
   denumr = return . map Quant . S.toDescList
-- 
-- 
-- Listas
-- ------
-- 
-- Definimos una lista de `Dimension`es como una `Dimensión`:
-- 
instance BoundedDimension a => Dimension [a] where
   type DimensionIx [a] = DimensionIx a
   type Dependent [a]   = Dependent a
   delem    ds i = anyM (withDep . (`delem` i)) ds
   dpred    ds i = do
      (as, bs) <- fmap ( partition ((>=i) . fromJust . fst)
                       . filter (isJust . fst)
                       . (`zip` ds)
                       ) (mapM (withDep . dlast) ds)
      preds    <- fmap catMaybes $ mapM (withDep . (`dpred` i) . snd) as
      return $ case preds of
                 []   -> case map fst bs of
                          [] -> Nothing
                          xs -> maximum xs
                 xs   -> Just $ maximum xs
   dsucc    ds i = do
      (as, bs) <- fmap ( partition ((<=i) . fromJust . fst)
                       . filter (isJust . fst)
                       . (`zip` ds)
                       ) (mapM (withDep . dfirst) ds)
      preds    <- fmap catMaybes $ mapM (withDep . (`dsucc` i) . snd) as
      return $ case preds of
                 []   -> case map fst bs of
                          [] -> Nothing
                          xs -> minimum xs
                 xs   -> Just $ minimum xs
   dfloor   ds i = do
     floors <- fmap catMaybes$ mapM (withDep . (`dfloor` i)) ds
     case floors of
       [] -> stopIteration
       xs -> yieldQuant . maximum . filter (<=i) . map unQ $ xs
   dceiling ds i = do
     ceils <- fmap catMaybes $ mapM (withDep . (`dceiling` i)) ds
     case ceils of
       [] -> stopIteration
       xs -> yieldQuant . minimum . filter (>=i) . map unQ $ xs
-- 
-- 
instance BoundedDimension a => BoundedDimension [a] where
   dfirst ds = do
     firsts <- fmap catMaybes $ mapM (withDep . dfirst) ds
     case firsts of
       [] -> stopIteration
       xs -> return . Just $ minimum xs
   dlast ds = do
     lasts <- fmap catMaybes $ mapM (withDep . dlast) ds
     case lasts of
       [] -> stopIteration
       xs -> return . Just $ maximum xs
