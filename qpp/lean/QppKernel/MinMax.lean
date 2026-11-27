module

public import QppKernel.Bal

/-!
# Least and greatest, by relation

No rational function is the minimum of two masses, so `min` is not a word of `1`, `+` and `/`. It is read as a
relation that needs only the order: `m` is the least of `a`, `b` when `m = a ≤ b` or `m = b ≤ a`, and the least of a
list when it is in the list and below every entry. That each exists and is unique is Mathlib's, read through the
order of the bridge (`lean/QppBridge`: `Count.toNat_le`, `Mass.toRat_le`, `Bal.tie_iff`); the order laws the kernel's
results use are here.
-/

@[expose] public section

namespace Qpp

variable {α : Type}

namespace Mass

theorem le_antisymm {a b : Mass} (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  rcases h1 with h1 | h1
  · exact h1
  · exact absurd h1 (not_lt_of_le h2)

theorem le_trans {a b c : Mass} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact Or.inr (lt_of_lt_of_le h1 h2)

end Mass

end Qpp
