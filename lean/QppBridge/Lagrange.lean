module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination

/-!
# The reading of the cited tie of divided differences

`fact_lagrange_tie`: Mathlib `Lagrange.coeff_eq_sum` at the polynomial `1`. On the nodes `0..q` with the gaps `r`,
the node `m` sits at the sum of the first `m` gaps (`gapNode`), and the product of the distances from the node `m`
to the other nodes is the product of the distances to the nodes on its left times the product of the distances to
the nodes on its right, with one sign per node on the right (`gapNode_erase`). Masses that tie on each pair of
neighbours differ by alternating signs (`tie_alt`), so the tie of the two sums is the coefficient of `X ^ q` in `1`,
which vanishes at `q >= 1`.
-/

@[expose] public section

open Finset Polynomial

namespace Qpp.Cite

/-- The node `m`: the sum of the first `m` gaps. -/
def gapNode (r : ℕ → ℚ) (m : ℕ) : ℚ := ∑ j ∈ Icc 1 m, r j

/-- The gaps from the node `a` to the node `b`. -/
theorem gapNode_sub (r : ℕ → ℚ) {a b : ℕ} (h : a ≤ b) :
    ∑ j ∈ Icc (a + 1) b, r j = gapNode r b - gapNode r a := by
  have h1 : ∀ c : ℕ, Icc 1 c = Ioc 0 c := fun c => Icc_add_one_left_eq_Ioc 0 c
  unfold gapNode
  rw [eq_sub_iff_add_eq, add_comm, Icc_add_one_left_eq_Ioc, h1, h1]
  exact sum_Ioc_consecutive r (Nat.zero_le a) h

theorem gapNode_strictMono (r : ℕ → ℚ) (hr : ∀ i, 0 < r i) : StrictMono (gapNode r) := by
  refine strictMono_nat_of_lt_succ (fun n => ?_)
  unfold gapNode
  rw [sum_Icc_succ_top (Nat.le_add_left 1 n)]
  exact lt_add_of_pos_right _ (hr (n + 1))

/-- The distances to the nodes on the left of `m`, as the gaps between them. -/
theorem gapNode_left (r : ℕ → ℚ) (m : ℕ) :
    ∏ g ∈ Icc 1 m, ∑ j ∈ Icc g m, r j = ∏ i ∈ Ico 0 m, (gapNode r m - gapNode r i) := by
  rw [← Ico_add_one_right_eq_Icc, ← zero_add 1, ← prod_Ico_add' (fun g => ∑ j ∈ Icc g m, r j) 0 m 1]
  refine prod_congr rfl (fun i hi => gapNode_sub r (le_of_lt (mem_Ico.mp hi).2))

/-- The distances to the nodes on the right of `m`, as the gaps between them. -/
theorem gapNode_right (r : ℕ → ℚ) (m q : ℕ) :
    ∏ g ∈ Icc (m + 1) q, ∑ j ∈ Icc (m + 1) g, r j = ∏ g ∈ Icc (m + 1) q, (gapNode r g - gapNode r m) :=
  prod_congr rfl (fun _ hg => gapNode_sub r (Nat.le_of_succ_le (mem_Icc.mp hg).1))

/-- The product of Lagrange's formula: the distances to the other nodes, one sign per node on the right. -/
theorem gapNode_erase (r : ℕ → ℚ) {m q : ℕ} (hm : m ≤ q) :
    ∏ j ∈ (Icc 0 q).erase m, (gapNode r m - gapNode r j) =
      (-1) ^ (q - m) * ((∏ g ∈ Icc 1 m, ∑ j ∈ Icc g m, r j) *
        ∏ g ∈ Icc (m + 1) q, ∑ j ∈ Icc (m + 1) g, r j) := by
  have hsplit : (Icc 0 q).erase m = Ico 0 m ∪ Icc (m + 1) q := by
    ext j
    simp only [mem_erase, mem_Icc, mem_union, mem_Ico]
    constructor
    · rintro ⟨hne, h0, hq⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr ⟨h, hq⟩
    · rintro (⟨h0, h⟩ | ⟨h, hq⟩)
      · exact ⟨ne_of_lt h, h0, le_trans (le_of_lt h) hm⟩
      · exact ⟨ne_of_gt h, Nat.zero_le j, hq⟩
  have hdisj : Disjoint (Ico 0 m) (Icc (m + 1) q) := by
    rw [disjoint_left]
    intro j h1 h2
    simp only [mem_Ico, mem_Icc] at h1 h2
    exact absurd h2.1 (not_le.mpr (Nat.lt_succ_of_lt h1.2))
  have hneg : ∏ j ∈ Icc (m + 1) q, (gapNode r m - gapNode r j) =
      (-1) ^ (q - m) * ∏ g ∈ Icc (m + 1) q, (gapNode r g - gapNode r m) := by
    rw [← Nat.card_Icc (m + 1) q |>.trans (Nat.add_sub_add_right q 1 m), ← prod_neg]
    exact prod_congr rfl (fun j _ => (neg_sub _ _).symm)
  rw [hsplit, prod_union hdisj, hneg, gapNode_left, gapNode_right]
  ring

/-- Masses that tie on each pair of neighbours differ by alternating signs. -/
theorem tie_alt (n : ℕ) (x y : ℕ → ℚ) (h : ∀ m : ℕ, m ≤ n → x m + x (m + 1) = y m + y (m + 1)) :
    ∀ m : ℕ, m ≤ n + 1 → x m - y m = (-1) ^ m * (x 0 - y 0) := by
  intro m
  induction m with
  | zero => intro _; rw [pow_zero, one_mul]
  | succ m ih =>
    intro hm
    have hmn : m ≤ n := Nat.le_of_succ_le_succ hm
    rw [pow_succ]
    linear_combination h m hmn - ih (Nat.le_succ_of_le hmn)

theorem fact_lagrange_tie : ∀ (n : ℕ) (r x y : ℕ → ℚ), (∀ i, 0 < (r i)) → (∀ i, 0 ≤ (x i)) → (∀ i, 0 ≤ (y i)) → (∀ m : ℕ, (m ≤ n) → (x m + x (m + (1 : ℕ)) = y m + y (m + (1 : ℕ)))) → (∑ m ∈ Finset.Icc (0 : ℕ) (n + (1 : ℕ)), x m / ((∏ g ∈ Finset.Icc (1 : ℕ) m, (∑ j ∈ Finset.Icc g m, r j)) * (∏ g ∈ Finset.Icc (m + (1 : ℕ)) (n + (1 : ℕ)), (∑ j ∈ Finset.Icc (m + (1 : ℕ)) g, r j)))) = (∑ m ∈ Finset.Icc (0 : ℕ) (n + (1 : ℕ)), y m / ((∏ g ∈ Finset.Icc (1 : ℕ) m, (∑ j ∈ Finset.Icc g m, r j)) * (∏ g ∈ Finset.Icc (m + (1 : ℕ)) (n + (1 : ℕ)), (∑ j ∈ Finset.Icc (m + (1 : ℕ)) g, r j)))) := by
  intro n r x y hr _ _ htie
  have hdeg : (1 : ℚ[X]).degree < (#(Icc 0 (n + 1)) : WithBot ℕ) := by
    rw [degree_one, Nat.card_Icc]
    exact WithBot.coe_lt_coe.mpr (Nat.succ_pos _)
  have hL := Lagrange.coeff_eq_sum ((gapNode_strictMono r hr).injective.injOn) hdeg
  rw [Nat.card_Icc, Nat.sub_zero, Nat.add_sub_cancel, coeff_one, ite_eq_right (Nat.succ_ne_zero n)] at hL
  simp only [eval_one] at hL
  rw [← sub_eq_zero, ← sum_sub_distrib]
  have hterm : ∀ m ∈ Icc 0 (n + 1),
      x m / ((∏ g ∈ Icc 1 m, ∑ j ∈ Icc g m, r j) * ∏ g ∈ Icc (m + 1) (n + 1), ∑ j ∈ Icc (m + 1) g, r j) -
        y m / ((∏ g ∈ Icc 1 m, ∑ j ∈ Icc g m, r j) * ∏ g ∈ Icc (m + 1) (n + 1), ∑ j ∈ Icc (m + 1) g, r j) =
      (-1) ^ (n + 1) * (x 0 - y 0) * (1 / ∏ j ∈ (Icc 0 (n + 1)).erase m, (gapNode r m - gapNode r j)) := by
    intro m hm
    have hmq : m ≤ n + 1 := (mem_Icc.mp hm).2
    have hq : ((-1 : ℚ) ^ (n + 1)) = (-1) ^ m * (-1) ^ (n + 1 - m) := by
      rw [← pow_add, Nat.add_sub_cancel' hmq]
    rw [gapNode_erase r hmq, ← sub_div, tie_alt n x y htie m hmq, hq]
    have hu0 : ((-1 : ℚ) ^ (n + 1 - m)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
    set L := (∏ g ∈ Icc 1 m, ∑ j ∈ Icc g m, r j) * ∏ g ∈ Icc (m + 1) (n + 1), ∑ j ∈ Icc (m + 1) g, r j
    linear_combination (-((-1) ^ m * (x 0 - y 0) * L⁻¹)) * mul_inv_cancel₀ hu0
  rw [sum_congr rfl hterm, ← mul_sum, ← hL, mul_zero]

end Qpp.Cite
