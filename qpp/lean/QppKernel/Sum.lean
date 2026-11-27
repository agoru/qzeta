module

public import QppKernel.Order

/-!
# Finite sums

There is no zero: the sum of no terms is absent, `none`, and absent is the unit of the sum (`oadd`). A sum over a
list is `osum`; it is present exactly when the list is not empty. The count of a list is the sum of one `1` per
entry (`card`). A sum or a product over the counts `1, ..., n` is never empty (`sumTo`, `prodTo`). The
definitions are in `Base.lean`. The laws of the sums over lists are here; those of `sumTo` and `prodTo` are
Mathlib's sums and products, read through the bridge (`lean/QppBridge/Sums.lean`: `map_sumTo`, `map_prodTo`).
-/

@[expose] public section

namespace Qpp

variable {α : Type} [Add α]

theorem osum_eq_none {l : List α} : osum l = none ↔ l = [] := by
  cases l with
  | nil => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | cons x l =>
    constructor
    · intro h; simp only [osum] at h; cases hl : osum l <;> rw [hl] at h <;> cases h
    · intro h; cases h

section Laws

variable (assoc : ∀ x y z : α, x + y + z = x + (y + z))

include assoc in
theorem oadd_assoc (x y z : Option α) : oadd (oadd x y) z = oadd x (oadd y z) := by
  cases x <;> cases y <;> cases z <;> simp only [oadd, assoc]

include assoc in
theorem osum_append (l m : List α) : osum (l ++ m) = oadd (osum l) (osum m) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.cons_append, osum, ih, oadd_assoc assoc]

end Laws

theorem Mass.osum_append (l m : List Mass) : osum (l ++ m) = oadd (osum l) (osum m) :=
  _root_.Qpp.osum_append Mass.add_assoc l m

theorem Count.osum_append (l m : List Count) : osum (l ++ m) = oadd (osum l) (osum m) :=
  _root_.Qpp.osum_append Count.add_assoc l m

end Qpp
