
module Errors where

import Control.Exception

import Syntax
import Common
import Values
import qualified Presyntax as P
import qualified Values as V

data Error
  = UnifyError Val Val
  | NameNotInScope P.Name
  | NoSuchField P.Name
  | NoNamedImplicitArg P.Name
  | IcitMismatch Icit Icit
  | NoNamedLambdaInference
  | ExpectedSg V.Ty          -- inferred type
  | ExpectedFunOrForall V.Ty -- inferred type
  | GenericError String
  | AmbiguousUniverse
  | ExpectedType

data ErrorInCxt = ErrorInCxt Locals P.Tm Error

instance Show ErrorInCxt where
  show = uf

instance Exception ErrorInCxt
