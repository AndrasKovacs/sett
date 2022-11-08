
module Errors (Error(..), ErrorInCxt(..)) where

import Control.Exception

import Syntax
import Common
import Values
import Pretty
import qualified Presyntax as P
import qualified Values as V

import qualified FlatParse.Stateful as FP
import qualified Data.ByteString.Char8 as B

import Evaluation

data Error
  = UnifyError Val Val UnifyEx
  | NameNotInScope P.Name
  | NoSuchField P.Name
  | NoNamedImplicitArg P.Name
  | IcitMismatch Icit Icit
  | NoNamedLambdaInference
  | ExpectedSg V.Ty          -- inferred type
  | ExpectedFun V.Ty         -- inferred type
  | GenericError String
  | AmbiguousUniverse
  | ExpectedSetProp
  | TypeIsNotProp

data ErrorInCxt = ErrorInCxt Src Locals Lvl P.Tm Error

instance Show ErrorInCxt where
  show (ErrorInCxt src ls l t err) =
    let ?locals = ls
        ?lvl = l in
    let showVal v = showTm (quoteWithOpt UnfoldMetas v)
        showValNf v = showTm (quoteWithOpt UnfoldEverything v)
        msg = case err of
          UnifyError t u ex ->
            "Can't unify inferred type\n\n  " ++ showVal t ++ "\n\nwith expected type\n\n  "
                                ++ showVal u ++ "\n" ++
            "\nNormal forms of sides: \n\n  " ++ showValNf t ++ "\n\nand\n\n  "
                                ++ showValNf u ++ "\n\n" ++
            show ex
            -- case ex of
            --   CantSolveFrozenMeta m -> "\nCan't solve frozen metavariable " ++ show m ++ "\n"
            --   _ -> ""
          NameNotInScope x ->
            "Name not in scope: " ++ "\"" ++ show x ++ "\""
          NoSuchField x ->
            "No such field name: " ++ "\"" ++ show x ++ "\""
          NoNamedImplicitArg x ->
            "No such named implicit argument: " ++ "\"" ++ show x ++ "\""
          IcitMismatch i i' ->
            "Function implicitness mismatch" -- TODO
          NoNamedLambdaInference ->
            "Can't infer type for lambda expression with named argument"
          ExpectedSg a ->
            "Expected a sigma type, inferred\n\n  " ++ showVal a ++ "\n"
          ExpectedFun a ->
            "Expected a function type, inferred\n\n  " ++ showVal a ++ "\n"
          GenericError msg ->
            msg
          AmbiguousUniverse ->
            "Ambiguous Set/Prop universe"
          ExpectedSetProp ->
            "Expected a type in Set or Prop"
          TypeIsNotProp ->
            "Expected a type in Prop"

    in render (srcToBs src) (P.span t) msg

instance Exception ErrorInCxt


-- | Display an error with source position. We only use of the first position in
--   the span.
render :: B.ByteString -> Span -> String -> String
render bs (Span pos _) msg = let
  ls     = FP.lines bs
  (l, c) = head $ FP.posLineCols bs [rawPos pos]
  line   = if l < length ls then ls !! l else ""
  linum  = show (l + 1)
  lpad   = map (const ' ') linum
  in linum  ++ ":" ++ show c ++ ":\n" ++
     lpad   ++ "|\n" ++
     linum  ++ "| " ++ line ++ "\n" ++
     lpad   ++ "| " ++ replicate c ' ' ++ "^\n" ++
     msg
{-# noinline render #-}
