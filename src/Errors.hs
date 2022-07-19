
module Errors where

import Control.Exception

import Syntax
import Common
import Values
import qualified Presyntax as P
import qualified Values as V

data UnifyEx = CantUnify | FrozenSolution | FlexSolution
  deriving (Eq, Show)
instance Exception UnifyEx

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

data ErrorInCxt = ErrorInCxt Locals P.Tm Error

instance Show ErrorInCxt where
  show = uf

instance Exception ErrorInCxt
