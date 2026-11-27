module

public import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

/-!
# The simp set of the bridge

`qpp_bridge` collects the transport lemmas: each one rewrites the reading of a word of the kernel over Mathlib into
the term that the Mathlib reading of the same construct prints, so that `simp only [qpp_bridge]` turns a statement
over the kernel into its reading over Mathlib.

`qpp_bridge_add` collects the readings at a size `n + n'` of two counts (`QppBridge/Join.lean`): an index, a tuple, a
quantifier, a sum and a box of that size read on `Fin (n.toNat + n'.toNat)`. The transfer of a statement adds it
only when the statement has such a size, since at a size `n + 1` the reading of a numeral is asked instead.
-/

public section

register_simp_attr qpp_bridge
register_simp_attr qpp_bridge_add
