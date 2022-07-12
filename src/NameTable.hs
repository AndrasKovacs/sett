
{-| Mapping from raw names -}

module NameTable where

import qualified Data.ByteString      as B
import qualified Data.HashMap.Strict  as HM

import Common
import qualified Presyntax as P
import qualified Syntax    as S
import qualified Values    as V

data Entry
  = Top S.Ty {-# unpack #-} V.GTy V.Val -- ^ Type, type val, value.
  | Local Lvl {-# unpack #-} V.GTy      -- ^ Level, type val.

type NameTable = HM.HashMap B.ByteString Entry

lookup :: P.Name -> NameTable -> Maybe Entry
lookup x = HM.lookup (P.nameToBs x)

insert :: P.Name -> Entry -> NameTable -> NameTable
insert  x entry = HM.insert (P.nameToBs x) entry
