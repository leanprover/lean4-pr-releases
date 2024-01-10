/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Transform
import Lean.Elab.Deriving.Basic
import Lean.Elab.Deriving.Util

namespace Lean.Elab.Deriving.BEq
open Lean.Parser.Term
open Meta

def mkBEqHeader (argNames : Array Name) (nestedOcc : NestedOccurence) : TermElabM Header := do
  mkHeader `BEq 2 argNames nestedOcc

def mkMatch (ctx : Context) (header : Header) (e : Expr) (fvars : Array Expr) : TermElabM Term := do
  let f := e.getAppFn
  let ind := f.constName!
  let lvls := f.constLevels!
  let indVal ← getConstInfoInduct ind
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts indVal lvls
  `(match $[$discrs],* with $alts:matchAlt*)
where
  mkElseAlt (indVal : InductiveVal): TermElabM (TSyntax ``matchAltExpr) := do
    let mut patterns := #[]
    -- add `_` pattern for indices
    for _ in [:indVal.numIndices] do
      patterns := patterns.push (← `(_))
    patterns := patterns.push (← `(_))
    patterns := patterns.push (← `(_))
    let altRhs ← `(false)
    `(matchAltExpr| | $[$patterns:term],* => $altRhs:term)

  mkAlts (indVal : InductiveVal) (lvl : List Level): TermElabM (Array (TSyntax ``matchAlt)) := do
    let mut alts := #[]
    for ctorName in indVal.ctors do
      let args := e.getAppArgs
      let ctorInfo ← getConstInfoCtor ctorName
      let ctorApp := mkAppN (mkConst ctorInfo.name lvl) args[:ctorInfo.numParams]
      let ctorType ← inferType ctorApp
      let alt ← forallTelescopeReducing ctorType fun xs type => do
        let type ← Core.betaReduce type -- we 'beta-reduce' to eliminate "artificial" dependencies
        let mut patterns := #[]
        -- add `_` pattern for indices
        for _ in [:indVal.numIndices] do
          patterns := patterns.push (← `(_))
        let mut ctorArgs1 := #[]
        let mut ctorArgs2 := #[]
        let mut rhs ← `(true)
        -- add `_` for inductive parameters, they are inaccessible
        for _ in [:indVal.numParams] do
          ctorArgs1 := ctorArgs1.push (← `(_))
          ctorArgs2 := ctorArgs2.push (← `(_))
        for i in [:ctorInfo.numFields] do
          let x := xs[i]!
          if type.containsFVar x.fvarId! then
            -- If resulting type depends on this field, we don't need to compare
            ctorArgs1 := ctorArgs1.push (← `(_))
            ctorArgs2 := ctorArgs2.push (← `(_))
          else
            let a := mkIdent (← mkFreshUserName `a)
            let b := mkIdent (← mkFreshUserName `b)
            ctorArgs1 := ctorArgs1.push a
            ctorArgs2 := ctorArgs2.push b
            if let some auxFunName ← ctx.getFunName? header (← inferType x) fvars then
              rhs ← `($rhs && $(mkIdent auxFunName):ident $a:ident $b:ident)
            else
              rhs ← `($rhs && $a:ident == $b:ident)
        patterns := patterns.push (← `(@$(mkIdent ctorName):ident $ctorArgs1:term*))
        patterns := patterns.push (← `(@$(mkIdent ctorName):ident $ctorArgs2:term*))
        `(matchAltExpr| | $[$patterns:term],* => $rhs:term)
      alts := alts.push alt
    alts := alts.push (← mkElseAlt indVal)
    return alts

def mkAuxFunction (ctx : Context) (i : Nat) : TermElabM Command := do
  let auxFunName := ctx.auxFunNames[i]!
  let nestedOcc  := ctx.typeInfos[i]!
  let argNames := ctx.typeArgNames[i]!
  let header     ←  mkBEqHeader argNames nestedOcc
  let binders    := header.binders
  Term.elabBinders binders fun xs => do
  let type ← Term.elabTerm header.targetType none
  let body       ←  mkMatch ctx header type xs
  `(private def $(mkIdent auxFunName):ident $binders:bracketedBinder* : Bool := $body:term)

def mkMutualBlock (ctx : Context) : TermElabM Syntax := do
  let mut auxDefs := #[]
  for i in [:ctx.typeInfos.size] do
    auxDefs := auxDefs.push (← mkAuxFunction ctx i)
  `(mutual
     set_option match.ignoreUnusedAlts true
     $auxDefs:command*
    end)

private def mkBEqInstanceCmds (declName : Name) : TermElabM (Array Syntax) := do
  let ctx ← mkContext "beq" declName
  let cmds := #[← mkMutualBlock ctx] ++ (← mkInstanceCmds ctx `BEq)
  trace[Elab.Deriving.beq] "\n{cmds}"
  return cmds

private def mkBEqEnumFun (ctx : Context) (name : Name) : TermElabM Syntax := do
  let auxFunName := ctx.auxFunNames[0]!
  `(private def $(mkIdent auxFunName):ident  (x y : $(mkIdent name)) : Bool := x.toCtorIdx == y.toCtorIdx)

private def mkBEqEnumCmd (name : Name): TermElabM (Array Syntax) := do
  let ctx ← mkContext "beq" name
  let cmds := #[← mkBEqEnumFun ctx name] ++ (← mkInstanceCmds ctx `BEq)
  trace[Elab.Deriving.beq] "\n{cmds}"
  return cmds

open Command

def mkBEqInstance (declName : Name) : CommandElabM Unit := do
    let cmds ← liftTermElabM <|
      if (← isEnumType declName) then
        mkBEqEnumCmd declName
      else
         mkBEqInstanceCmds declName
    cmds.forM elabCommand

def mkBEqInstanceHandler (declNames : Array Name) : CommandElabM Bool := do
  if (← declNames.allM isInductive) then
    for declName in declNames do
      mkBEqInstance declName
    return true
  else
    return false

builtin_initialize
  registerDerivingHandler `BEq mkBEqInstanceHandler
  registerTraceClass `Elab.Deriving.beq

end Lean.Elab.Deriving.BEq
