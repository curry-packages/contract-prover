-----------------------------------------------------------------------------
--- Definition of data types ocurring in type-annotated FlatCurry programs.
---
--- @author  Michael Hanus
--- @version May 2019
---------------------------------------------------------------------------

module FlatCurry.Typed.Types
  ( module FlatCurry.Typed.Types
  , module FlatCurry.Annotated.Types
  )
 where

import FlatCurry.Types
import FlatCurry.Annotated.Types

-- Type synomyms for type-annotated FlatCurry entities:
type TAProg       = AProg       TypeExpr
type TAFuncDecl   = AFuncDecl   TypeExpr
type TARule       = ARule       TypeExpr
type TAExpr       = AExpr       TypeExpr
type TABranchExpr = ABranchExpr TypeExpr
type TAPattern    = APattern    TypeExpr

----------------------------------------------------------------------------
