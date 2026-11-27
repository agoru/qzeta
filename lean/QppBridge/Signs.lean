module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Polynomial.RuleOfSigns
public import Mathlib.Algebra.Polynomial.EraseLead
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Rat.Lemmas
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Algebra.Order.Ring.Basic
public import Mathlib.Data.Nat.Log

/-!
# The readings of the cited facts on families of coefficients

A cited fact of `table` is stated on families of coefficients, and the Mathlib lemma that proves it on a polynomial
or on the forward difference. This file reads each statement from its lemma, once. Each lemma here relates two
encodings of one notion. The generated `X.holds` of the cit is `exact Qpp.Cite.X`.

- `fact_fwddiff_core`: Mathlib `fwdDiff_iter_pow_eq_zero_of_lt` with `fwdDiff_iter_eq_sum_shift`. The encodings are
  the alternating sum and the two sums by the parity of the index (`alt_sum_split`).
- `fact_descartes_1`: Mathlib `Polynomial.roots_countP_pos_le_signVariations`, Descartes' rule of signs. The
  encodings are:
  - a family of coefficients on the exponents `0..D` and its polynomial (`ofFamily`);
  - the forms at the binomial coefficients and the Taylor coefficients at `1` (`ofFamily_comp_coeff`), so their
    vanishing up to order `l` and a zero of order `l + 1` at `1` (`dvd_of_forms`, `le_signVariations_of_dvd`);
  - a labelling of the exponents, nondecreasing, at most `s`, with one side per label, and the changes of side
    (`signVariations_add_le_of_runs`).
- `fact_hockey_1`: Mathlib `Nat.sum_Icc_choose`, the hockey stick. The encodings are a range `0..D` cut at `j` by a
  bracket and the range `i..j`, whose terms below `i` vanish.
- `fact_jensen_1`: Mathlib `pow_sum_le_card_mul_sum_pow`, Jensen's inequality for sums of powers. The encodings are
  a family on the range `1..N` and its number of terms, `N`.
- `fact_jensentwo_1`: Mathlib `add_pow_le`, Jensen's inequality for two powers. The encodings are the power `m + 1`
  and the factor `2 ^ (m + 1 - 1)` of the lemma.
- `fact_vandermonde_1`: Mathlib `Nat.sum_range_choose_sq`, Vandermonde's identity for the squares of a row. The
  encodings are the range `0..p` and `range (p + 1)`.
- `fact_sqrttwo_1`: Mathlib `Rat.isSquare_ofNat_iff`. The encodings are a rational with the square `2` and the
  square `2` in the rationals and in the naturals, where it is decided.
- `fact_digits_1`: Mathlib `Nat.log`, with `Nat.log_pos`, `Nat.pow_log_le_self` and `Nat.lt_pow_succ_log_self`. The
  encodings are the count `A` of the digits of `x` in the base `b` and `Nat.log b (b * x)`.
-/

@[expose] public section

namespace Qpp.Cite

open Finset Polynomial

theorem sum_range_two_mul (g : ℕ → ℚ) (n : ℕ) :
    ∑ k ∈ range (2 * n), g k = ∑ j ∈ range n, (g (2 * j) + g (2 * j + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih, sum_range_succ]
    ring

theorem alt_sum_split (f : ℕ → ℚ) (l : ℕ) (hf : ∀ k, l < k → f k = 0) :
    ∑ k ∈ range (l + 1), (-1 : ℚ) ^ k * f k
      = ∑ j ∈ Icc 0 l, f (2 * j) - ∑ j ∈ Icc 0 l, f (2 * j + 1) := by
  have h1 : ∑ k ∈ range (l + 1), (-1 : ℚ) ^ k * f k = ∑ k ∈ range (2 * (l + 1)), (-1 : ℚ) ^ k * f k := by
    apply sum_subset
    · intro k hk; simp only [mem_range] at hk ⊢; omega
    · intro k hk hk'; simp only [mem_range, not_lt] at hk hk'; rw [hf k (by omega), mul_zero]
  rw [h1, sum_range_two_mul]
  rw [show Icc 0 l = range (l + 1) by ext; simp]
  rw [← sum_sub_distrib]
  refine sum_congr rfl (fun j _ => ?_)
  rw [pow_succ, pow_mul]; norm_num; ring

/-- The forward difference of order `l` of a power below `l` vanishes; its binomial weights split by parity. -/
theorem fact_fwddiff_core : ∀ (l i : ℕ) (y : ℚ), (0 ≤ y) → (i < l) → (∑ j ∈ Finset.Icc (0 : ℕ) l, (Nat.choose l ((2 : ℕ) * j) : ℚ) * (y + (2 : ℚ) * (j : ℚ)) ^ i) = (∑ j ∈ Finset.Icc (0 : ℕ) l, (Nat.choose l ((2 : ℕ) * j + (1 : ℕ)) : ℚ) * (y + (2 : ℚ) * (j : ℚ) + (1 : ℚ)) ^ i) := by
  intro l i y _ hil
  set f : ℕ → ℚ := fun k => (l.choose k : ℚ) * (y + (k : ℚ)) ^ i with hf
  have hz : ∀ k, l < k → f k = 0 := fun k hk => by simp [hf, Nat.choose_eq_zero_of_lt hk]
  have hsplit := alt_sum_split f l hz
  have h0 := congrFun (fwdDiff_iter_pow_eq_zero_of_lt (R := ℚ) hil) y
  rw [fwdDiff_iter_eq_sum_shift] at h0
  have hzero : ∑ k ∈ range (l + 1), (-1 : ℚ) ^ k * f k = 0 := by
    have e0 : ∑ k ∈ range (l + 1), (-1 : ℚ) ^ k * f k = (-1) ^ l * ∑ k ∈ range (l + 1),
        ((-1 : ℤ) ^ (l - k) * (l.choose k : ℤ)) • (y + k • (1 : ℚ)) ^ i := by
      rw [mul_sum]
      refine sum_congr rfl (fun k hk => ?_)
      have hk' : k ≤ l := by simp only [mem_range] at hk; omega
      have e : (-1 : ℚ) ^ l = (-1) ^ (l - k) * (-1) ^ k := by rw [← pow_add, Nat.sub_add_cancel hk']
      have hsq : ((-1 : ℚ) ^ (l - k)) * ((-1) ^ (l - k)) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      rw [e, zsmul_eq_mul, nsmul_eq_mul, mul_one, hf]
      push_cast
      linear_combination (-((-1 : ℚ) ^ k * (l.choose k : ℚ) * (y + k) ^ i)) * hsq
    rw [e0]
    simp only [Pi.zero_apply] at h0
    rw [h0, mul_zero]
  rw [hzero] at hsplit
  have h1 := (sub_eq_zero.mp hsplit.symm)
  simp only [hf] at h1
  push_cast at h1
  convert h1 using 3 <;> ring

/-- The changes of side of the coefficients, at most the rise of a labelling of the exponents that is nondecreasing
and has one side per label. -/
theorem signVariations_add_le_of_runs (N : ℕ) (ρ : ℕ → ℕ)
    (hmono : ∀ m n, m ≤ N → n ≤ N → m ≤ n → ρ m ≤ ρ n) :
    ∀ (P : ℚ[X]), P.natDegree ≤ N →
      (∀ m n, m ≤ N → n ≤ N → ρ m = ρ n → ¬ (0 < P.coeff m ∧ P.coeff n < 0)) →
      P.signVariations + ρ 0 ≤ ρ P.natDegree := by
  intro P
  induction h : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    intro hN hside
    by_cases hP : P = 0
    · subst hP; simp at h; subst h; simp
    rw [signVariations_eq_eraseLead_add_ite hP]
    have hlead : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP
    by_cases hQ0 : P.eraseLead = 0
    · have hne : ¬ (SignType.sign P.leadingCoeff = -SignType.sign P.eraseLead.leadingCoeff) := by
        rw [hQ0, leadingCoeff_zero, sign_zero, neg_zero, sign_eq_zero_iff]
        exact hlead
      rw [ite_eq_right_iff.2 (fun h' => absurd h' hne), hQ0, signVariations_zero]
      have := hmono 0 n (Nat.zero_le _) (h ▸ hN) (Nat.zero_le _)
      omega
    have hlt : P.eraseLead.natDegree < n := by
      rcases eraseLead_natDegree_lt_or_eraseLead_eq_zero P with h1 | h1
      · omega
      · exact absurd h1 hQ0
    have hcoeff : ∀ m, P.eraseLead.coeff m = if m = P.natDegree then 0 else P.coeff m := by
      intro m
      split_ifs with hm
      · rw [hm]; exact eraseLead_coeff_natDegree
      · exact eraseLead_coeff_of_ne m hm
    have hsideQ : ∀ m n, m ≤ N → n ≤ N → ρ m = ρ n →
        ¬ (0 < P.eraseLead.coeff m ∧ P.eraseLead.coeff n < 0) := by
      intro m n' hm hn hρ ⟨h1, h2⟩
      rw [hcoeff] at h1 h2
      split_ifs at h1 h2 <;> first | exact lt_irrefl _ h1 | exact lt_irrefl _ h2 | exact hside m n' hm hn hρ ⟨h1, h2⟩
    have ihQ := ih _ hlt P.eraseLead rfl (by omega) hsideQ
    have hmQ := hmono _ _ (by omega) (h ▸ hN) hlt.le
    split_ifs with hs
    · -- opposite signs at the two leading exponents: two labels
      have hQlead : P.eraseLead.leadingCoeff = P.coeff P.eraseLead.natDegree := by
        rw [leadingCoeff, hcoeff, ite_eq_right_iff.mpr (fun h' => absurd h' (by omega))]
      have hQne : P.eraseLead.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ0
      have hρ : ρ P.eraseLead.natDegree ≠ ρ n := by
        intro hρ
        rw [hQlead] at hs hQne
        have hPl : P.leadingCoeff = P.coeff n := by rw [leadingCoeff, h]
        rw [hPl] at hs hlead
        rcases lt_or_gt_of_ne hlead with hp | hp <;> rcases lt_or_gt_of_ne hQne with hq | hq
        · rw [sign_neg hp, sign_neg hq] at hs; simp at hs
        · exact hside _ _ (by omega) (h ▸ hN) hρ ⟨hq, hp⟩
        · exact hside _ _ (h ▸ hN) (by omega) hρ.symm ⟨hp, hq⟩
        · rw [sign_pos hp, sign_pos hq] at hs; simp at hs
      have : ρ P.eraseLead.natDegree < ρ n := lt_of_le_of_ne hmQ hρ
      omega
    · omega


/-- The polynomial of a family of coefficients on the exponents `0..D`. -/
noncomputable def ofFamily (D : ℕ) (f : ℕ → ℚ) : ℚ[X] := ∑ m ∈ Icc 0 D, C (f m) * X ^ m

theorem ofFamily_coeff (D : ℕ) (f : ℕ → ℚ) (k : ℕ) :
    (ofFamily D f).coeff k = if k ≤ D then f k else 0 := by
  simp only [ofFamily, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [sum_ite_eq (Icc 0 D) k (fun m => f m)]
  simp

theorem ofFamily_natDegree_le (D : ℕ) (f : ℕ → ℚ) : (ofFamily D f).natDegree ≤ D := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro k hk
  rw [ofFamily_coeff, ite_eq_right_iff.2 (fun h' => absurd h' (by
    have : D < k := by exact_mod_cast hk
    omega))]

/-- `l` is at most the changes of side of the coefficients of a nonzero polynomial with a zero of order `l` at `1`:
Descartes' rule of signs. -/
theorem le_signVariations_of_dvd (R : ℚ[X]) (hR : R ≠ 0) (l : ℕ) (h : (X - C 1) ^ l ∣ R) :
    l ≤ R.signVariations := by
  refine le_trans ?_ (roots_countP_pos_le_signVariations R)
  have h1 := Multiset.countP_le_of_le (fun x : ℚ => 0 < x) (roots.le_of_dvd hR h)
  refine le_trans (le_of_eq ?_) h1
  rw [roots_pow, roots_X_sub_C, Multiset.countP_nsmul]
  have h2 : Multiset.countP (fun x : ℚ => 0 < x) {1} = 1 :=
    (Multiset.countP_cons_of_pos (s := 0) (by norm_num : (0 : ℚ) < 1)).trans (by simp)
  rw [h2, mul_one]


/-- The forms at the binomial coefficients are the coefficients of the polynomial at `X + 1`: its Taylor
coefficients at `1`. -/
theorem ofFamily_comp_coeff (D : ℕ) (A : ℕ → ℚ) (i : ℕ) :
    ((ofFamily D A).comp (X + 1)).coeff i = ∑ m ∈ Icc 0 D, A m * (m.choose i : ℚ) := by
  simp only [ofFamily, Polynomial.sum_comp, mul_comp, C_comp, pow_comp, X_comp, finsetSum_coeff, coeff_C_mul,
    coeff_X_add_one_pow]

/-- A zero of order `l + 1` at `1`, read at its Taylor coefficients. -/
theorem dvd_of_forms (D l : ℕ) (A : ℕ → ℚ) (hA : ∀ i ≤ l, ∑ m ∈ Icc 0 D, A m * (m.choose i : ℚ) = 0) :
    (X - C 1) ^ (l + 1) ∣ ofFamily D A := by
  have h1 : X ^ (l + 1) ∣ (ofFamily D A).comp (X + 1) := by
    rw [X_pow_dvd_iff]; intro d hd; rw [ofFamily_comp_coeff]; exact hA d (by omega)
  have h2 := map_dvd (compRingHom (X - C 1)) h1
  simp only [coe_compRingHom_apply, pow_comp, X_comp, comp_assoc, add_comp, one_comp, map_one,
    sub_add_cancel, comp_X] at h2
  exact h2

theorem fact_descartes_1 : ∀ (D l s : ℕ) (AP AN : ℕ → ℚ) (rho : ℕ → ℕ), (∀ i, 0 ≤ (AP i)) → (∀ i, 0 ≤ (AN i)) → (∀ i : ℕ, (i ≤ l) → ((∑ m ∈ Finset.Icc (0 : ℕ) D, AP m * (Nat.choose m i : ℚ)) = (∑ m ∈ Finset.Icc (0 : ℕ) D, AN m * (Nat.choose m i : ℚ)))) → (∃ m : ℕ, (m ≤ D) ∧ (0 < AP m + AN m)) → (∀ m : ℕ, (m ≤ D) → (∀ n : ℕ, (n ≤ D) → ((m ≤ n) → (rho m ≤ rho n)))) → (∀ m : ℕ, (m ≤ D) → (rho m ≤ s)) → (∀ m : ℕ, (m ≤ D) → (∀ n : ℕ, (n ≤ D) → ((rho m = rho n) → (AP m * AN n = (0 : ℚ))))) → l + (1 : ℕ) ≤ s := by
  intro D l s AP AN rho hAP hAN hforms ⟨m0, hm0, hpos⟩ hmono hle hside
  set A : ℕ → ℚ := fun m => AP m - AN m with hAdef
  have hQ : ofFamily D A ≠ 0 := by
    intro h0
    have := congrArg (fun P => P.coeff m0) h0
    simp only [ofFamily_coeff, hm0, ↓reduceIte, coeff_zero, hAdef] at this
    have h00 := hside m0 hm0 m0 hm0 rfl
    rcases mul_eq_zero.1 h00 with h | h <;> linarith [hAP m0, hAN m0]
  have hA : ∀ i ≤ l, ∑ m ∈ Icc 0 D, A m * (m.choose i : ℚ) = 0 := by
    intro i hi
    simp only [hAdef, sub_mul, sum_sub_distrib, hforms i hi, sub_self]
  have h2 := le_signVariations_of_dvd _ hQ (l + 1) (dvd_of_forms D l A hA)
  have h3 := signVariations_add_le_of_runs D rho (fun m n hm hn hmn => hmono m hm n hn hmn) (ofFamily D A)
    (ofFamily_natDegree_le D A) (by
      intro m n hm hn hr ⟨hp, hq⟩
      simp only [ofFamily_coeff, hm, ↓reduceIte] at hp
      simp only [ofFamily_coeff, hn, ↓reduceIte] at hq
      have hpm : 0 < AP m := by simp only [hAdef] at hp; linarith [hAN m]
      have hpn : 0 < AN n := by simp only [hAdef] at hq; linarith [hAP n]
      exact (mul_pos hpm hpn).ne' (hside m hm n hn hr))
  have h4 := hle _ (ofFamily_natDegree_le D A)
  omega


/-- The hockey stick: the range `0..D` cut at `j` by a bracket is the range `0..j`, whose terms below `i` vanish. -/
theorem fact_hockey_1 : ∀ (D j i : ℕ), (j ≤ D) → (∑ m ∈ Finset.Icc (0 : ℕ) D, (if m ≤ j then (1 : ℚ) else 0) * (Nat.choose m i : ℚ)) = (Nat.choose (j + (1 : ℕ)) (i + (1 : ℕ)) : ℚ) := by
  intro D j i hj
  have hcut : (∑ m ∈ Icc (0 : ℕ) D, (if m ≤ j then (1 : ℚ) else 0) * (Nat.choose m i : ℚ))
      = ∑ m ∈ Icc (0 : ℕ) j, (Nat.choose m i : ℚ) := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [← Finset.sum_filter]
    congr 1
    ext m
    simp only [mem_filter, mem_Icc]
    omega
  have hlow : ∑ m ∈ Icc (0 : ℕ) j, (Nat.choose m i : ℚ) = ∑ m ∈ Icc i j, (Nat.choose m i : ℚ) := by
    symm
    apply Finset.sum_subset
    · intro m hm; simp only [mem_Icc] at hm ⊢; omega
    · intro m hm hm'
      simp only [mem_Icc, not_and, not_le] at hm hm'
      have : m < i := by
        by_contra h
        exact absurd (hm' (by omega)) (by omega)
      simp [Nat.choose_eq_zero_of_lt this]
  rw [hcut, hlow]
  exact_mod_cast Nat.sum_Icc_choose j i

/-- Jensen's inequality for sums of powers, on the range `1..N`, which has `N` terms. -/
theorem fact_jensen_1 : ∀ (N m : ℕ) (e : ℕ → ℚ), (∀ i, 0 < (e i)) → (∑ j ∈ Finset.Icc (1 : ℕ) N, e j) ^ (m + (1 : ℕ)) ≤ (N : ℚ) ^ m * (∑ j ∈ Finset.Icc (1 : ℕ) N, e j ^ (m + (1 : ℕ))) := by
  intro N m e he
  have h := pow_sum_le_card_mul_sum_pow (s := Finset.Icc 1 N) (fun i _ => (he i).le) m
  simpa using h

/-- Jensen's inequality for two powers, at the power `m + 1`, whose factor `2 ^ (m + 1 - 1)` is `2 ^ m`. -/
theorem fact_jensentwo_1 : ∀ (m : ℕ) (x y : ℚ), (0 ≤ x) → (0 ≤ y) → (x + y) ^ (m + (1 : ℕ)) ≤ (2 : ℚ) ^ m * (x ^ (m + (1 : ℕ)) + y ^ (m + (1 : ℕ))) := by
  intro m x y hx hy
  have h := add_pow_le hx hy (m + 1)
  rwa [Nat.add_sub_cancel] at h

/-- No rational has the square `2`: `2` is a square in the rationals only if it is one in the naturals. -/
theorem fact_sqrttwo_1 : ∀ (c : ℚ), (0 ≤ c) → c ^ 2 ≠ (2 : ℚ) := by
  intro c _ h
  have h2 : IsSquare (2 : ℚ) := ⟨c, by rw [← h]; ring⟩
  rw [Rat.isSquare_ofNat_iff] at h2
  exact absurd h2 (by decide +kernel)

/-- Vandermonde's identity for the squares of a row, on the range `0..p`, which is `range (p + 1)`. -/
theorem fact_vandermonde_1 : ∀ (p : ℕ), (∑ i ∈ Finset.Icc (0 : ℕ) p, Nat.choose p i ^ 2) = Nat.choose ((2 : ℕ) * p) p := by
  intro p
  rw [← Nat.sum_range_choose_sq p]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_Icc, Finset.mem_range]
  omega

/-- The count of the digits of `x` in the base `b` puts `b * x` between two consecutive powers of `b`: it is the
readout `Nat.log b (b * x)`, at least `1` since `b <= b * x`. -/
theorem fact_digits_1 : ∀ (b x : ℕ), (1 ≤ b) → (1 ≤ x) → ((2 : ℕ) ≤ b) → ∃ A : ℕ, (1 ≤ A) ∧ (b ^ A ≤ b * x) ∧ (b * x < b ^ (A + (1 : ℕ))) := by
  intro b x hb1 hx hb
  have hbx : b ≤ b * x := Nat.le_mul_of_pos_right b hx
  exact ⟨Nat.log b (b * x), Nat.log_pos hb hbx,
    Nat.pow_log_le_self b (Nat.pos_iff_ne_zero.mp (Nat.mul_pos hb1 hx)),
    Nat.lt_pow_succ_log_self hb (b * x)⟩

end Qpp.Cite
