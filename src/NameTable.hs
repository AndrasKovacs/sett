
{-| Mapping from raw names -}

module NameTable where

import qualified Data.ByteString      as B
import qualified Data.HashMap.Strict  as HM

import Common
import qualified Syntax    as S
import qualified Values    as V

data Entry
  = Top S.Ty {-# unpack #-} V.GTy V.Val -- ^ Type, type val, value.
  | Local Lvl {-# unpack #-} V.GTy      -- ^ Level, type val.

type NameTable = HM.HashMap B.ByteString Entry

lookup :: Span -> NameTable -> Maybe Entry
lookup x = HM.lookup (spanToBs x)

insert :: Bind -> Entry -> NameTable -> NameTable
insert x entry tbl = case x of
  Bind x   -> HM.insert (spanToBs x) entry tbl
  DontBind -> tbl
