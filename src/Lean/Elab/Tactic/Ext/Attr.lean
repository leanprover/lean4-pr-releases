/-
Copyright (c) 2021 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Mario Carneiro
-/
import Lean.Elab.Tactic.RCases
import Lean.Meta.DiscrTree
import Lean.Elab.Command

namespace Lean.Elab.Tactic.Ext
open Lean Meta

/--
`declare_ext_theorems_for A` declares the extensionality theorems for the structure `A`.

These theorems state that two expressions with the structure type are equal if their fields are equal.
-/
syntax "declare_ext_theorems_for " ("(" &"flat" " := " term ") ")? ident (ppSpace prio)? : command

/-- Information about an extensionality theorem, stored in the environment extension. -/
structure ExtTheorem where
  /-- Declaration name of the extensionality theorem. -/
  declName : Name
  /-- Priority of the extensionality theorem. -/
  priority : Nat
  /--
  Key in the discrimination tree,
  for the type in which the extensionality theorem holds.
  -/
  keys : Array DiscrTree.Key
  deriving Inhabited, Repr, BEq, Hashable

/-- The state of the `ext` extension environment -/
structure ExtTheorems where
  /-- The tree of `ext` extensions. -/
  tree   : DiscrTree ExtTheorem := {}
  /-- Erased `ext`s via `attribute [-ext]`. -/
  erased  : PHashSet Name := {}
  deriving Inhabited

/-- Discrimation tree settings for the `ext` extension. -/
def extExt.config : WhnfCoreConfig := {}

/-- The environment extension to track `@[ext]` theorems. -/
initialize extExtension :
    SimpleScopedEnvExtension ExtTheorem ExtTheorems ←
  registerSimpleScopedEnvExtension {
    addEntry := fun { tree, erased } thm =>
      { tree := tree.insertCore thm.keys thm, erased := erased.erase thm.declName }
    initial := {}
  }

/-- Gets the list of `@[ext]` theorems corresponding to the key `ty`,
ordered from high priority to low. -/
@[inline] def getExtTheorems (ty : Expr) : MetaM (Array ExtTheorem) := do
  let extTheorems := extExtension.getState (← getEnv)
  let arr ← extTheorems.tree.getMatch ty extExt.config
  let erasedArr := arr.filter fun thm => !extTheorems.erased.contains thm.declName
  -- Using insertion sort because it is stable and the list of matches should be mostly sorted.
  -- Most ext theorems have default priority.
  return erasedArr.insertionSort (·.priority < ·.priority) |>.reverse

/--
Erases a name marked `ext` by adding it to the state's `erased` field and
removing it from the state's list of `Entry`s.

This is triggered by `attribute [-ext] name`.
-/
def ExtTheorems.eraseCore (d : ExtTheorems) (declName : Name) : ExtTheorems :=
 { d with erased := d.erased.insert declName }

/--
  Erases a name marked as a `ext` attribute.
  Check that it does in fact have the `ext` attribute by making sure it names a `ExtTheorem`
  found somewhere in the state's tree, and is not erased.
-/
def ExtTheorems.erase [Monad m] [MonadError m] (d : ExtTheorems) (declName : Name) :
    m ExtTheorems := do
  unless d.tree.containsValueP (·.declName == declName) && !d.erased.contains declName do
    throwError "'{declName}' does not have [ext] attribute"
  return d.eraseCore declName

/-- Registers an extensionality theorem.

* When `@[ext]` is applied to a structure, it generates `.ext` and `.ext_iff` theorems and registers
  them for the `ext` tactic.

* When `@[ext]` is applied to a theorem, the theorem is registered for the `ext` tactic.

* An optional natural number argument, e.g. `@[ext 9000]`, specifies a priority for the lemma. Higher-priority lemmas are chosen first, and the default is `1000`.

* The flag `@[ext (flat := false)]` causes generated structure extensionality theorems to show inherited fields based on their representation,
  rather than flattening the parents' fields into the lemma's equality hypotheses.
  structures in the generated extensionality theorems. -/
syntax (name := ext) "ext" (" (" &"flat" " := " term ")")? (ppSpace prio)? : attr

initialize registerBuiltinAttribute {
  name := `ext
  descr := "Marks a theorem as an extensionality theorem"
  add := fun declName stx kind => do
    let `(attr| ext $[(flat := $f)]? $(prio)?) := stx
      | throwError "unexpected @[ext] attribute {stx}"
    if isStructure (← getEnv) declName then
      liftCommandElabM <| Elab.Command.elabCommand <|
        ← `(declare_ext_theorems_for $[(flat := $f)]? $(mkCIdentFrom stx declName) $[$prio]?)
    else MetaM.run' do
      if let some flat := f then
        throwErrorAt flat "unexpected 'flat' config on @[ext] theorem"
      let declTy := (← getConstInfo declName).type
      let (_, _, declTy) ← withDefault <| forallMetaTelescopeReducing declTy
      let failNotEq := throwError
        "@[ext] attribute only applies to structures or theorems proving x = y, got {declTy}"
      let some (ty, lhs, rhs) := declTy.eq? | failNotEq
      unless lhs.isMVar && rhs.isMVar do failNotEq
      let keys ← withReducible <| DiscrTree.mkPath ty extExt.config
      let priority ← liftCommandElabM do Elab.liftMacroM do
        evalPrio (prio.getD (← `(prio| default)))
      extExtension.add {declName, keys, priority} kind
  erase := fun declName => do
    let s := extExtension.getState (← getEnv)
    let s ← s.erase declName
    modifyEnv fun env => extExtension.modifyState env fun _ => s
}
