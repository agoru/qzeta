module

public import QppKernel.FarkasTactic

/-!
# Pairs and ties

A pair `⟨l, r⟩` of counts or of masses stands for `l` less `r`; two pairs are tied when `a.l + b.r = b.l + a.r`.
Taking away is not a word of `1`, `+` and `/`; the pairs are its positive presentation (the integers are the pairs
of counts up to ties, the rationals the pairs of masses), a pair `⟨x, x⟩` stands for nothing, and no zero is added.
Sum, product and the order respect ties. An identity with differences on both sides, as a resultant or a square of a
difference, is a tie of pairs. Only the laws that the tactics and the kernel's own results use, and those of the
pairs of counts, are proved here; the laws of the pairs of masses are Mathlib's, read through `Bal.toRat`
(`lean/QppBridge/Pair.lean`).
-/

@[expose] public section

namespace Qpp

namespace Bal

variable {α : Type}

@[simp] theorem add_l [Add α] (a b : Bal α) : (a + b).l = a.l + b.l := rfl
@[simp] theorem add_r [Add α] (a b : Bal α) : (a + b).r = a.r + b.r := rfl
@[simp] theorem mul_l [Add α] [Mul α] (a b : Bal α) : (a * b).l = a.l * b.l + a.r * b.r := rfl
@[simp] theorem mul_r [Add α] [Mul α] (a b : Bal α) : (a * b).r = a.l * b.r + a.r * b.l := rfl
@[simp] theorem swap_l (a : Bal α) : (swap a).l = a.r := rfl
@[simp] theorem swap_r (a : Bal α) : (swap a).r = a.l := rfl
@[simp] theorem of_l [Add α] [OfNat α 1] (x : α) : (of x).l = x + 1 := rfl
@[simp] theorem of_r [Add α] [OfNat α 1] (x : α) : (of x).r = 1 := rfl
@[simp] theorem level_l [OfNat α 1] : (level : Bal α).l = 1 := rfl
@[simp] theorem level_r [OfNat α 1] : (level : Bal α).r = 1 := rfl
theorem pow_zero [Add α] [Mul α] [OfNat α 1] (a : Bal α) : a ^ 0 = ⟨1 + 1, 1⟩ := rfl
theorem pow_succ [Add α] [Mul α] [OfNat α 1] (a : Bal α) (k : Nat) : a ^ (k + 1) = a ^ k * a := rfl

end Bal

/-! ## The rationals: pairs of masses -/

namespace Mass

open Bal

theorem bal_tie_refl (a : Bal Mass) : a.Tie a := rfl

theorem bal_tie_symm {a b : Bal Mass} (h : a.Tie b) : b.Tie a := h.symm

theorem bal_tie_trans {a b c : Bal Mass} (h1 : a.Tie b) (h2 : b.Tie c) : a.Tie c := by
  unfold Tie at *
  apply add_right_cancel (z := b.l + b.r)
  calc a.l + c.r + (b.l + b.r) = (a.l + b.r) + (b.l + c.r) := by qeq
    _ = (b.l + a.r) + (c.l + b.r) := by rw [h1, h2]
    _ = c.l + a.r + (b.l + b.r) := by qeq

theorem bal_add_tie {a a' b b' : Bal Mass} (ha : a.Tie a') (hb : b.Tie b') : (a + b).Tie (a' + b') := by
  unfold Tie at *
  simp only [add_l, add_r]
  calc a.l + b.l + (a'.r + b'.r) = (a.l + a'.r) + (b.l + b'.r) := by qeq
    _ = (a'.l + a.r) + (b'.l + b.r) := by rw [ha, hb]
    _ = a'.l + b'.l + (a.r + b.r) := by qeq

theorem bal_mul_tie_left {a a' : Bal Mass} (b : Bal Mass) (ha : a.Tie a') : (a * b).Tie (a' * b) := by
  unfold Tie at *
  simp only [mul_l, mul_r]
  calc a.l * b.l + a.r * b.r + (a'.l * b.r + a'.r * b.l)
      = (a.l + a'.r) * b.l + (a'.l + a.r) * b.r := by qeq
    _ = (a'.l + a.r) * b.l + (a.l + a'.r) * b.r := by rw [ha]
    _ = a'.l * b.l + a'.r * b.r + (a.l * b.r + a.r * b.l) := by qeq

theorem bal_add_assoc (a b c : Bal Mass) : (a + b + c).Tie (a + (b + c)) := by
  unfold Tie; simp only [add_l, add_r]; qeq

theorem bal_level_add (a : Bal Mass) : (level + a).Tie a := by
  unfold Tie; simp only [add_l, add_r, level_l, level_r]; qeq

theorem bal_lt_irrefl (a : Bal Mass) : ¬ a < a := lt_irrefl (a.l + a.r)

theorem bal_trichotomy (a b : Bal Mass) : a < b ∨ a.Tie b ∨ b < a := by
  rcases trichotomy (a.l + b.r) (b.l + a.r) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem bal_of_lt {x y : Mass} : of x < of y ↔ x < y := by
  constructor
  · intro h
    have h' : x + 1 + 1 < y + 1 + 1 := h
    farkas [h']
  · intro h
    show x + 1 + 1 < y + 1 + 1
    farkas [h]

end Mass

/-! ## The integers: pairs of counts -/

namespace Count

open Bal

theorem bal_tie_refl (a : Bal Count) : a.Tie a := rfl

theorem bal_tie_symm {a b : Bal Count} (h : a.Tie b) : b.Tie a := h.symm

theorem bal_tie_trans {a b c : Bal Count} (h1 : a.Tie b) (h2 : b.Tie c) : a.Tie c := by
  unfold Tie at *
  apply add_right_cancel (c := b.l + b.r)
  calc a.l + c.r + (b.l + b.r) = (a.l + b.r) + (b.l + c.r) := by qeq
    _ = (b.l + a.r) + (c.l + b.r) := by rw [h1, h2]
    _ = c.l + a.r + (b.l + b.r) := by qeq

theorem bal_add_tie {a a' b b' : Bal Count} (ha : a.Tie a') (hb : b.Tie b') : (a + b).Tie (a' + b') := by
  unfold Tie at *
  simp only [add_l, add_r]
  calc a.l + b.l + (a'.r + b'.r) = (a.l + a'.r) + (b.l + b'.r) := by qeq
    _ = (a'.l + a.r) + (b'.l + b.r) := by rw [ha, hb]
    _ = a'.l + b'.l + (a.r + b.r) := by qeq

theorem bal_mul_tie_left {a a' : Bal Count} (b : Bal Count) (ha : a.Tie a') : (a * b).Tie (a' * b) := by
  unfold Tie at *
  simp only [mul_l, mul_r]
  calc a.l * b.l + a.r * b.r + (a'.l * b.r + a'.r * b.l)
      = (a.l + a'.r) * b.l + (a'.l + a.r) * b.r := by qeq
    _ = (a'.l + a.r) * b.l + (a.l + a'.r) * b.r := by rw [ha]
    _ = a'.l * b.l + a'.r * b.r + (a.l * b.r + a.r * b.l) := by qeq

theorem bal_mul_comm (a b : Bal Count) : (a * b).Tie (b * a) := by
  unfold Tie; simp only [mul_l, mul_r]; qeq

theorem bal_mul_tie {a a' b b' : Bal Count} (ha : a.Tie a') (hb : b.Tie b') : (a * b).Tie (a' * b') :=
  bal_tie_trans (bal_mul_tie_left b ha)
    (bal_tie_trans (bal_mul_comm a' b) (bal_tie_trans (bal_mul_tie_left a' hb) (bal_mul_comm b' a')))

theorem bal_lt_trans {a b c : Bal Count} (h1 : a < b) (h2 : b < c) : a < c := by
  have h1' : a.l + b.r < b.l + a.r := h1
  have h2' : b.l + c.r < c.l + b.r := h2
  show a.l + c.r < c.l + a.r
  farkas [h1', h2']

theorem bal_trichotomy (a b : Bal Count) : a < b ∨ a.Tie b ∨ b < a := by
  rcases trichotomy (a.l + b.r) (b.l + a.r) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end Count

end Qpp
