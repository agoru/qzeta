module

import QppBridge
import all QppBridge.Attr
import all QppBridge.Count
import all QppBridge.Mass
import all QppBridge.Sums
import all QppBridge.Box
import all QppBridge.Join
import all QppBridge.Pair
import all QppBridge.Prog
import all QppBridge.Signs
import all QppBridge.Lagrange
import all QppBridge.Rank
import all QppBridge.BidetMath
import all QppBridge.Bidet
public import Lean

/-!
# The axiom audit of the bridge

Every declaration of the modules `QppBridge.*` depends on no axiom other than `propext`, `Classical.choice` and
`Quot.sound`; the command fails otherwise. Each submodule is imported with `import all`, so that
its private declarations are audited too. Run from `lean`, after `lake build`:

    lake env lean QppBridge/Axioms.lean
-/

open Lean Elab Command

elab "#audit_bridge_axioms" : command => do
  let env ← getEnv
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  for (name, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod.getRoot == `QppBridge do continue
    let axioms ← liftCoreM (collectAxioms name)
    checked := checked + 1
    let extra := axioms.filter (!allowed.contains ·)
    unless extra.isEmpty do bad := bad.push (name, extra)
  unless bad.isEmpty do
    throwError m!"declarations with other axioms: {bad.toList}"
  if checked == 0 then
    throwError m!"no declaration of QppBridge found"
  logInfo m!"{checked} declarations of QppBridge: only propext, Classical.choice, Quot.sound"

#audit_bridge_axioms
