module Sigym4.Dimension (
    Quantized
  , unQuant
  , module Types
  , module Time
) where
import Sigym4.Dimension.Types as Types hiding ( Quantized(..)
                                              , justQuant
                                              , constQuant)
import Sigym4.Dimension.Time as Time
-- No exponemos en el API simple el constructor de Quantized para que la
-- única manera de obtenerlos sea a traves de 'Dimension'.
-- Para implementar instancias de Dimension el constructor se puede importar
-- directamente desde Types
import Sigym4.Dimension.Types (Quantized(unQuant))
