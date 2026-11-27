module

public import QppKernel.Sum

/-!
# Arch, Floor and Scale

* `Arch`: copies of a mass exceed any mass.
* `Floor`: a mass below `1` has no floor (it is absent); any other mass lies in exactly one `[n, n + 1)` with `n` a
  count.
* `Scale`: every mass lies in exactly one dyadic interval `d / 2 < x ≤ d`, the dyadic masses being `2^a / 2^b`.

All three are proved from the counts: by `ind` on the numerator (`Floor`), and by a least exponent (`Scale`), where
the exponents are Lean's numerals.
-/

@[expose] public section

namespace Qpp

namespace Count

theorem toNat_le {a b : Count} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  constructor
  · rintro (rfl | h)
    · exact Nat.le_refl _
    · exact Nat.le_of_lt (toNat_lt.mp h)
  · intro h
    rcases Nat.lt_or_eq_of_le h with h | h
    · exact Or.inr (toNat_lt.mpr h)
    · exact Or.inl (toNat_inj h)

theorem toNat_two : (2 : Count).toNat = 2 := rfl

end Count

namespace Mass

theorem mk_le_mk {p q r s : Count} : mk p q ≤ mk r s ↔ p * s ≤ r * q := by
  constructor
  · rintro (h | h)
    · exact Or.inl (mk_eq_mk.mp h)
    · exact Or.inr (mk_lt_mk.mp h)
  · rintro (h | h)
    · exact Or.inl (mk_eq_mk.mpr h)
    · exact Or.inr (mk_lt_mk.mpr h)

/-- The two sides of an order of masses `p / q` and `r / s`, as Lean's numerals. -/
theorem mk_lt_mk_nat {p q r s : Count} : mk p q < mk r s ↔ p.toNat * s.toNat < r.toNat * q.toNat := by
  rw [mk_lt_mk, Count.toNat_lt, Count.toNat_mul, Count.toNat_mul]

theorem mk_le_mk_nat {p q r s : Count} : mk p q ≤ mk r s ↔ p.toNat * s.toNat ≤ r.toNat * q.toNat := by
  rw [mk_le_mk, Count.toNat_le, Count.toNat_mul, Count.toNat_mul]

theorem two_mul_mk (p q : Count) : 2 * mk p q = mk (2 * p) q := by
  rw [show (2 : Mass) = mk 2 1 from rfl, mul_mk, mk_eq_mk]; qeq

/-! ## Arch -/

/-- `Arch`: for masses `d` and `R`, some count of copies of `d` exceeds `R`. -/
theorem arch (d R : Mass) : ∃ N : Count, R < ofCount N * d := by
  induction R using ind_mk with | h p q =>
  induction d using ind_mk with | h r s =>
  refine ⟨Count.succ (p * s), ?_⟩
  rw [show ofCount (Count.succ (p * s)) * mk r s = mk (Count.succ (p * s) * r) (1 * s) from mul_mk _ _ _ _,
    mk_lt_mk_nat]
  simp only [Count.toNat_mul, Count.toNat_succ, show (1 : Count).toNat = 1 from rfl]
  have hr := Count.toNat_pos r
  have hq := Count.toNat_pos q
  have h1 : 1 ≤ r.toNat * q.toNat := Nat.mul_pos hr hq
  calc p.toNat * (1 * s.toNat) = p.toNat * s.toNat := by rw [Nat.one_mul]
    _ < (p.toNat * s.toNat + 1) * 1 := by omega
    _ ≤ (p.toNat * s.toNat + 1) * (r.toNat * q.toNat) := Nat.mul_le_mul_left _ h1
    _ = (p.toNat * s.toNat + 1) * r.toNat * q.toNat := by rw [Nat.mul_assoc]

/-! ## Floor -/

theorem floor_counts (q : Count) :
    ∀ p : Count, p < q ∨ ∃ n : Count, n * q ≤ p ∧ p < (n + 1) * q := by
  intro p
  induction p using Count.ind with
  | h1 =>
    cases q with
    | one => exact Or.inr ⟨1, Or.inl rfl, ⟨1, rfl⟩⟩
    | succ q => exact Or.inl (Count.one_lt_succ q)
  | hs p ih =>
    rcases ih with h | ⟨n, hle, hlt⟩
    · rcases Count.succ_le_of_lt h with h | h
      · refine Or.inr ⟨1, Or.inl (by rw [h, Count.one_mul]), ?_⟩
        rw [h, Count.add_mul, Count.one_mul]; exact Count.lt_add q q
      · exact Or.inl h
    · rcases Count.succ_le_of_lt hlt with h | h
      · refine Or.inr ⟨n + 1, Or.inl h.symm, ?_⟩
        rw [h, Count.add_mul (n + 1) 1, Count.one_mul]; exact Count.lt_add _ q
      · exact Or.inr ⟨n, Or.inr (Count.lt_of_le_of_lt hle (Count.lt_succ p)), h⟩

/-- `Floor`: a mass is below `1`, or lies in `[n, n + 1)` for a count `n`. -/
theorem floor (t : Mass) : t < 1 ∨ ∃ n : Count, ofCount n ≤ t ∧ t < ofCount n + 1 := by
  induction t using ind_mk with | h p q =>
  rcases floor_counts q p with h | ⟨n, hle, hlt⟩
  · left
    rw [one_def, mk_lt_mk_nat]
    have := Count.toNat_lt.mp h
    simpa [show (1 : Count).toNat = 1 from rfl] using this
  · right
    refine ⟨n, ?_, ?_⟩
    · rw [show ofCount n = mk n 1 from rfl, mk_le_mk_nat]
      have := Count.toNat_le.mp hle
      simp only [Count.toNat_mul, show (1 : Count).toNat = 1 from rfl, Nat.mul_one] at this ⊢
      exact this
    · rw [show ofCount n + 1 = mk (n * 1 + 1 * 1) (1 * 1) from rfl, mk_lt_mk_nat]
      have := Count.toNat_lt.mp hlt
      simp only [Count.toNat_mul, Count.toNat_add, show (1 : Count).toNat = 1 from rfl, Nat.mul_one] at this ⊢
      exact this

theorem one_le_ofCount (n : Count) : 1 ≤ ofCount n := by
  rcases Count.one_le n with h | h
  · exact Or.inl (by rw [← h]; rfl)
  · exact Or.inr (ofCount_lt.mpr h)

/-- The floor is unique, and a mass with a floor is not below `1`. -/
theorem floor_unique {t : Mass} {n m : Count} (hn : ofCount n ≤ t ∧ t < ofCount n + 1)
    (hm : ofCount m ≤ t ∧ t < ofCount m + 1) : n = m := by
  have key : ∀ {a b : Count}, ofCount a ≤ t → t < ofCount b + 1 → ¬ b < a := by
    intro a b ha hb hba
    have h1 : ofCount (Count.succ b) ≤ ofCount a := by
      rcases Count.succ_le_of_lt hba with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (ofCount_lt.mpr h)
    rw [ofCount_succ] at h1
    exact lt_irrefl _ (lt_of_le_of_lt h1 (lt_of_le_of_lt ha hb))
  rcases Count.trichotomy n m with h | h | h
  · exact absurd h (key hm.1 hn.2)
  · exact h
  · exact absurd h (key hn.1 hm.2)

theorem not_floor_of_lt_one {t : Mass} (h : t < 1) (n : Count) : ¬ ofCount n ≤ t :=
  fun hn => lt_irrefl _ (lt_of_le_of_lt (one_le_ofCount n) (lt_of_le_of_lt hn h))

/-! ## Scale -/

/-- The dyadic masses `2^a / 2^b`, for numerals `a, b` of Lean. -/
def Dyadic (d : Mass) : Prop := ∃ a b : Nat, d = mk (2 ^ a) (2 ^ b)

theorem exists_least {P : Nat → Prop} {n : Nat} (h : P n) : ∃ m, P m ∧ ∀ k, k < m → ¬ P k := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hk : ∃ k, k < n ∧ P k
    · obtain ⟨k, hk, hPk⟩ := hk
      exact ih k hk hPk
    · exact ⟨n, h, fun k hk' hPk => hk ⟨k, hk', hPk⟩⟩

theorem toNat_two_pow (a : Nat) : ((2 : Count) ^ a).toNat = 2 ^ a := by
  rw [Count.toNat_pow, Count.toNat_two]

/-- `Scale`: every mass `x` has a dyadic `d` with `d / 2 < x ≤ d`. -/
theorem scale (x : Mass) : ∃ d, Dyadic d ∧ d < 2 * x ∧ x ≤ d := by
  induction x using ind_mk with | h p q =>
  -- the exponents, on Lean's numerals
  have hP : ∃ a, p.toNat * 2 ^ q.toNat ≤ 2 ^ a * q.toNat := by
    refine ⟨p.toNat * 2 ^ q.toNat, ?_⟩
    have := Nat.lt_two_pow_self (n := p.toNat * 2 ^ q.toNat)
    have hq := Count.toNat_pos q
    calc p.toNat * 2 ^ q.toNat ≤ 2 ^ (p.toNat * 2 ^ q.toNat) := Nat.le_of_lt this
      _ ≤ 2 ^ (p.toNat * 2 ^ q.toNat) * q.toNat := Nat.le_mul_of_pos_right _ hq
  obtain ⟨a0, ha0⟩ := hP
  obtain ⟨a, ha, hmin⟩ := exists_least (P := fun a => p.toNat * 2 ^ q.toNat ≤ 2 ^ a * q.toNat) ha0
  refine ⟨mk (2 ^ a) (2 ^ q.toNat), ⟨a, q.toNat, rfl⟩, ?_, ?_⟩
  · rw [two_mul_mk, mk_lt_mk_nat, toNat_two_pow, toNat_two_pow, Count.toNat_mul, Count.toNat_two]
    cases a with
    | zero =>
      have := Nat.lt_two_pow_self (n := q.toNat)
      have hp := Count.toNat_pos p
      simp only [Nat.pow_zero, Nat.one_mul]
      calc q.toNat < 2 ^ q.toNat := this
        _ ≤ 2 * p.toNat * 2 ^ q.toNat := Nat.le_mul_of_pos_left _ (by omega)
    | succ a =>
      have h := Nat.lt_of_not_le (hmin a (Nat.lt_succ_self a))
      rw [Nat.pow_succ]
      calc 2 ^ a * 2 * q.toNat = 2 * (2 ^ a * q.toNat) := by rw [Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]
        _ < 2 * (p.toNat * 2 ^ q.toNat) := by omega
        _ = 2 * p.toNat * 2 ^ q.toNat := by rw [Nat.mul_assoc]
  · rw [mk_le_mk_nat, toNat_two_pow, toNat_two_pow]; exact ha

theorem le_mul_le {x y : Mass} (h : x ≤ y) (z : Mass) : x * z ≤ y * z := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · exact Or.inr (mul_lt_mul_right z h)

/-- The dyadic interval of `Scale` is unique. -/
theorem scale_unique {x d e : Mass} (hd : Dyadic d) (he : Dyadic e) (h1 : d < 2 * x) (h2 : x ≤ d)
    (h3 : e < 2 * x) (h4 : x ≤ e) : d = e := by
  obtain ⟨a, b, rfl⟩ := hd
  obtain ⟨a', b', rfl⟩ := he
  have hde : mk (2 ^ a) (2 ^ b) < 2 * mk (2 ^ a') (2 ^ b') := by
    have := le_mul_le h4 2
    rw [mul_comm x 2, mul_comm _ 2] at this
    exact lt_of_lt_of_le h1 this
  have hed : mk (2 ^ a') (2 ^ b') < 2 * mk (2 ^ a) (2 ^ b) := by
    have := le_mul_le h2 2
    rw [mul_comm x 2, mul_comm _ 2] at this
    exact lt_of_lt_of_le h3 this
  rw [two_mul_mk, mk_lt_mk_nat, Count.toNat_mul, toNat_two_pow, toNat_two_pow, toNat_two_pow, toNat_two_pow,
    Count.toNat_two] at hde hed
  rw [mk_eq_mk]
  apply Count.toNat_inj
  rw [Count.toNat_mul, Count.toNat_mul, toNat_two_pow, toNat_two_pow, toNat_two_pow, toNat_two_pow,
    ← Nat.pow_add, ← Nat.pow_add]
  have e1 : ∀ m n : Nat, 2 * 2 ^ m * 2 ^ n = 2 ^ (m + n + 1) := fun m n => by
    rw [Nat.pow_succ, Nat.pow_add, Nat.mul_comm 2 (2 ^ m), Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm 2 (2 ^ n)]
  rw [e1, ← Nat.pow_add] at hde hed
  have h5 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hde
  have h6 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hed
  congr 1
  omega

end Mass

end Qpp
