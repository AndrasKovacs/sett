
module Cxt.Types where

import Common
import Syntax
import Values
import NameTable

data Cxt = Cxt {
  _env       :: Env,
  _lvl       :: Lvl,
  _locals    :: Locals,
  _nameTable :: NameTable
  }
