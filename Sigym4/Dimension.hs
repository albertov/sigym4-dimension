module Sigym4.Dimension (
    Quantized
  , Schedule
  , unQuant
  , module Types
  , module Time
) where
import Sigym4.Dimension.Types as Types hiding ( Quantized(..)
                                              , yieldQuant
                                              , stopIteration
                                              , getDep )
import Sigym4.Dimension.Time as Time hiding (Schedule(..))
-- No exponemos en el API simple el constructor de Quantized para que la
-- única manera de obtenerlos sea a traves de 'Dimension'.
-- Para implementar instancias de Dimension el constructor se puede importar
-- directamente desde Types
import Sigym4.Dimension.Types (Quantized(unQuant))

import Sigym4.Dimension.Time (Schedule)
