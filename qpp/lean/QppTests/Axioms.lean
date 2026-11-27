module

import QppKernel
import QppTests
import all QppKernel.Base
import all QppKernel.Identity
import all QppKernel.Tactic
import all QppKernel.Mass
import all QppKernel.MassTactic
import all QppKernel.Laws
import all QppKernel.Instance
import all QppKernel.Order
import all QppKernel.Sum
import all QppKernel.Scale
import all QppKernel.Farkas
import all QppKernel.FarkasTactic
import all QppKernel.Bal
import all QppKernel.MinMax
import all QppKernel.BalTactic
import all QppKernel.Patterns
import all QppKernel.Poly
import all QppKernel.Law
import all QppKernel.Sparse
import all QppKernel.Cite
import all QppKernel.Pin
import all QppKernel.Words
import all QppTests.Smoke
import all QppTests.Resultant
import all QppTests.FarkasSmoke
import all QppTests.Farkas
import all QppTests.Sparse
import all QppTests.PairSmoke
import all QppTests.Pin
public import Lean

/-!
# The axiom audit of qpp/lean

Every declaration of the modules `QppKernel.*` and `QppTests.*` depends on no axiom other than `propext`,
`Classical.choice` and `Quot.sound`; the command fails otherwise. Each submodule is imported with `import all`, so that
its private declarations are audited too. Run from `qpp/lean`, after `lake build`:

    lake env lean QppTests/Axioms.lean
-/

open Lean Elab Command

elab "#audit_axioms" : command => do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod.getRoot == `QppKernel || mod.getRoot == `QppTests do continue
    let axioms ← liftCoreM (collectAxioms name)
    checked := checked + 1
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do bad := bad.push (name, extra)
  unless bad.isEmpty do
    throwError m!"declarations with other axioms: {bad.toList}"
  logInfo m!"{checked} declarations of QppKernel and QppTests: only propext, Classical.choice, Quot.sound"

#audit_axioms
