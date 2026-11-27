module

public import QppKernel.Order

/-!
# Farkas certificates

A certificate for `L < R` or `L ≤ R` from hypotheses `aⱼ < bⱼ`, `aⱼ ≤ bⱼ` or `aⱼ = bⱼ` is a coefficient `cⱼ` for
each hypothesis and a slack `s` with `R + Σ cⱼ aⱼ = L + Σ cⱼ bⱼ + s` an identity. With no zero the slack is a sum of monomials, or absent; when it is absent, `<` needs a strict
hypothesis. The identity is checked as by `qeq` (`CExpr.verify`); the tactic `farkas` finds the slack. The slack
also carries the positivity of the variables, so the certificate is complete for linear inequalities over the
masses (Farkas' lemma). On a box `lo < x < hi`, `x = (lo c' + hi c) / (c + c')` for two masses `c`, `c'`
(`Mass.box`): positivity on a box is a certificate in `c`, `c'` with no hypothesis, the slack being the
Bernstein coefficients. A box splits at a point into two boxes and the point (`Mass.split`), and a count below `n + 1` is below `n` or is
`n` (`Count.lt_succ_cases`).
-/

@[expose] public section

namespace Qpp

namespace Count

theorem le_refl (a : Count) : a ≤ a := Or.inl rfl

theorem le_of_lt {a b : Count} (h : a < b) : a ≤ b := Or.inr h

theorem le_of_eq {a b : Count} (h : a = b) : a ≤ b := Or.inl h

theorem add_lt_add_left {a b : Count} (c : Count) (h : a < b) : c + a < c + b := by
  rw [add_comm c a, add_comm c b]; exact add_lt_add_right c h

theorem add_lt_of_lt_le {a b c d : Count} (h1 : a < b) : c ≤ d → a + c < b + d
  | Or.inl rfl => add_lt_add_right c h1
  | Or.inr h2 => lt_trans (add_lt_add_right c h1) (add_lt_add_left b h2)

theorem add_lt_of_le_lt {a b c d : Count} (h1 : a ≤ b) (h2 : c < d) : a + c < b + d := by
  rw [add_comm a c, add_comm b d]; exact add_lt_of_lt_le h2 h1

theorem add_le_le {a b c d : Count} : a ≤ b → c ≤ d → a + c ≤ b + d
  | Or.inl rfl, Or.inl rfl => Or.inl rfl
  | h1, Or.inr h2 => Or.inr (add_lt_of_le_lt h1 h2)
  | Or.inr h1, h2 => Or.inr (add_lt_of_lt_le h1 h2)

theorem mul_lt_mul_left {a b : Count} (c : Count) (h : a < b) : c * a < c * b := by
  rw [mul_comm c a, mul_comm c b]; exact mul_lt_mul_right c h

theorem mul_le_mul_left {a b : Count} (c : Count) : a ≤ b → c * a ≤ c * b
  | Or.inl rfl => Or.inl rfl
  | Or.inr h => Or.inr (mul_lt_mul_left c h)

/-- A finite case split: a count below `n + 1` is below `n` or is `n`. -/
theorem lt_succ_cases {x n : Count} (h : x < succ n) : x < n ∨ x = n := by
  rcases trichotomy x n with h' | h' | h'
  · exact Or.inl h'
  · exact Or.inr h'
  · exact absurd h (not_lt_of_le (succ_le_of_lt h'))

theorem not_lt_one (x : Count) : ¬ x < 1
  | ⟨c, h⟩ => by
    cases c with
    | one => exact succ_ne_one x h.symm
    | succ c => exact succ_ne_one (x + c) h.symm

/-- The last step of a certificate with a slack. -/
theorem lt_of_add {L R A B : Count} (hAB : A ≤ B) (h : L + B < R + A) : L < R := by
  rcases trichotomy L R with h' | rfl | h'
  · exact h'
  · exact absurd h (not_lt_of_le (add_le_le (le_refl L) hAB))
  · exact absurd h (lt_asymm (add_lt_of_lt_le h' hAB))

/-- The last step of a certificate with no slack and a strict hypothesis. -/
theorem lt_of_add_tie {L R A B : Count} (hAB : A < B) (h : R + A = L + B) : L < R :=
  lt_of_add_lt_add_right (c := A) (h ▸ add_lt_add_left L hAB)

/-- The last step of a certificate with no slack. -/
theorem le_of_add_tie {L R A B : Count} : A ≤ B → R + A = L + B → L ≤ R
  | Or.inl rfl, h => Or.inl (add_right_cancel h).symm
  | Or.inr hAB, h => Or.inr (lt_of_add_tie hAB h)

end Count

namespace Mass

theorem le_refl (a : Mass) : a ≤ a := Or.inl rfl

theorem le_of_lt {a b : Mass} (h : a < b) : a ≤ b := Or.inr h

theorem le_of_eq {a b : Mass} (h : a = b) : a ≤ b := Or.inl h

theorem add_lt_add_left {a b : Mass} (c : Mass) (h : a < b) : c + a < c + b := by
  rw [add_comm c a, add_comm c b]; exact add_lt_add_right c h

theorem add_lt_of_lt_le {a b c d : Mass} (h1 : a < b) : c ≤ d → a + c < b + d
  | Or.inl rfl => add_lt_add_right c h1
  | Or.inr h2 => lt_trans (add_lt_add_right c h1) (add_lt_add_left b h2)

theorem add_lt_of_le_lt {a b c d : Mass} (h1 : a ≤ b) (h2 : c < d) : a + c < b + d := by
  rw [add_comm a c, add_comm b d]; exact add_lt_of_lt_le h2 h1

theorem add_le_le {a b c d : Mass} : a ≤ b → c ≤ d → a + c ≤ b + d
  | Or.inl rfl, Or.inl rfl => Or.inl rfl
  | h1, Or.inr h2 => Or.inr (add_lt_of_le_lt h1 h2)
  | Or.inr h1, h2 => Or.inr (add_lt_of_lt_le h1 h2)

theorem mul_lt_mul_left {a b : Mass} (c : Mass) (h : a < b) : c * a < c * b := by
  rw [mul_comm c a, mul_comm c b]; exact mul_lt_mul_right c h

theorem mul_le_mul_left {a b : Mass} (c : Mass) : a ≤ b → c * a ≤ c * b
  | Or.inl rfl => Or.inl rfl
  | Or.inr h => Or.inr (mul_lt_mul_left c h)

theorem lt_of_add {L R A B : Mass} (hAB : A ≤ B) (h : L + B < R + A) : L < R := by
  rcases trichotomy L R with h' | rfl | h'
  · exact h'
  · exact absurd h (not_lt_of_le (add_le_le (le_refl L) hAB))
  · exact absurd h (lt_asymm (add_lt_of_lt_le h' hAB))

theorem lt_of_add_tie {L R A B : Mass} (hAB : A < B) (h : R + A = L + B) : L < R :=
  lt_of_add_lt_add_right (z := A) (h ▸ add_lt_add_left L hAB)

theorem le_of_add_tie {L R A B : Mass} : A ≤ B → R + A = L + B → L ≤ R
  | Or.inl rfl, h => Or.inl (add_right_cancel h).symm
  | Or.inr hAB, h => Or.inr (lt_of_add_tie hAB h)

/-- A point of an open box is a weighted mean of its ends: `x - lo = c` and `hi - x = c'`. -/
theorem box {lo x hi : Mass} (h1 : lo < x) (h2 : x < hi) : ∃ c c' : Mass, x = (lo * c' + hi * c) / (c + c') := by
  obtain ⟨c, rfl⟩ := h1
  obtain ⟨c', rfl⟩ := h2
  exact ⟨c, c', by qeq⟩

/-- An open box split at a point. -/
theorem split {lo x hi : Mass} (m : Mass) (h1 : lo < x) (h2 : x < hi) :
    (lo < x ∧ x < m) ∨ x = m ∨ (m < x ∧ x < hi) := by
  rcases trichotomy x m with h | h | h
  · exact Or.inl ⟨h1, h⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨h, h2⟩)

end Mass

theorem Count.eq_of_comb {L R A B : Count} (hAB : A = B) (h : L + B = R + A) : L = R :=
  Count.add_right_cancel (hAB ▸ h)

theorem Mass.eq_of_comb {L R A B : Mass} (hAB : A = B) (h : L + B = R + A) : L = R :=
  Mass.add_right_cancel (hAB ▸ h)

theorem add_eq_add {α : Type} [Add α] {a b c d : α} (h₁ : a = b) (h₂ : c = d) : a + c = b + d := h₁ ▸ h₂ ▸ rfl

theorem mul_eq_mul {α : Type} [Mul α] (c : α) {a b : α} (h : a = b) : c * a = c * b := h ▸ rfl

namespace CExpr

theorem lt_of_check (m : CheckBy) (ρ : Nat → Count) (L R A B s : CExpr) (hAB : eval ρ A ≤ eval ρ B)
    (h : verify m (.add R A) (.add (.add L B) s) = true) : eval ρ L < eval ρ R :=
  Count.lt_of_add hAB ⟨eval ρ s, eq_of_verify m ρ _ _ h⟩

theorem lt_of_check_tie (m : CheckBy) (ρ : Nat → Count) (L R A B : CExpr) (hAB : eval ρ A < eval ρ B)
    (h : verify m (.add R A) (.add L B) = true) : eval ρ L < eval ρ R :=
  Count.lt_of_add_tie hAB (eq_of_verify m ρ _ _ h)

theorem le_of_check_tie (m : CheckBy) (ρ : Nat → Count) (L R A B : CExpr) (hAB : eval ρ A ≤ eval ρ B)
    (h : verify m (.add R A) (.add L B) = true) : eval ρ L ≤ eval ρ R :=
  Count.le_of_add_tie hAB (eq_of_verify m ρ _ _ h)

end CExpr

namespace MExpr

/-- With `num (R + A) * den (L + B) = num (L + B) * den (R + A) + s` an identity of counts, `L < R`. -/
theorem lt_of_check (m : CheckBy) (σ : List Mass) (L R A B : MExpr) (s : CExpr) (hAB : eval σ A ≤ eval σ B)
    (h : CExpr.verify m (cross (.add R A) (.add L B)).1 (.add (cross (.add R A) (.add L B)).2 s) = true) :
    eval σ L < eval σ R := by
  apply Mass.lt_of_add hAB
  obtain ⟨ρ, hρ⟩ := exists_common σ
  show eval σ (.add L B) < eval σ (.add R A)
  rw [eval_common σ ρ hρ (.add L B), eval_common σ ρ hρ (.add R A), Mass.mk_lt_mk]
  exact ⟨_, CExpr.eq_of_verify m ρ _ _ h⟩

theorem lt_of_check_tie (m : CheckBy) (σ : List Mass) (L R A B : MExpr) (hAB : eval σ A < eval σ B)
    (h : CExpr.verify m (cross (.add R A) (.add L B)).1 (cross (.add R A) (.add L B)).2 = true) :
    eval σ L < eval σ R :=
  Mass.lt_of_add_tie hAB (eq_of_check m σ _ _ h)

theorem le_of_check_tie (m : CheckBy) (σ : List Mass) (L R A B : MExpr) (hAB : eval σ A ≤ eval σ B)
    (h : CExpr.verify m (cross (.add R A) (.add L B)).1 (cross (.add R A) (.add L B)).2 = true) :
    eval σ L ≤ eval σ R :=
  Mass.le_of_add_tie hAB (eq_of_check m σ _ _ h)

end MExpr

end Qpp
