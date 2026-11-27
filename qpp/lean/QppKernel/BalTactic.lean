module

public import QppKernel.Bal
public import QppKernel.MinMax
public import QppKernel.Laws
public import QppKernel.Order
public meta import QppKernel.FarkasTactic

/-!
# Identities and inequalities of pairs

A statement over the rationals is one over pairs of masses (`Base.lean`). Its checks unfold the pairs into their
two masses and replay the certificate there:

* `peq` proves a tie `a.Tie b` of pair expressions: the components (`add_l`, `mul_r`, ...) turn it into one identity
  of masses, `a.l + b.r = b.l + a.r`, which `qeq` checks; `peq [h, c • h']` uses the ties `h`, `h'`, unfolded the
  same way, as `qeq [..]` does.
* `pfarkas [..]` proves `a ≤ b` or `a < b` of pairs: `≤` and `<` of pairs are `≤` and `<` of the same masses
  (`le_def`, `lt_def`), and `farkas` replays the certificate there.
* The multipliers that are not hypotheses are the squares (`sq_nonneg`) and the products of nonnegative pairs
  (`mul_nonneg`): a certificate of degree two, still checked by one linear combination.
-/

@[expose] public section

namespace Qpp

namespace Bal

theorem le_def {a b : Bal Mass} : a ≤ b ↔ a.l + b.r ≤ b.l + a.r := Iff.rfl

theorem lt_def {a b : Bal Mass} : a < b ↔ a.l + b.r < b.l + a.r := Iff.rfl

theorem tie_def {a b : Bal Mass} : a.Tie b ↔ a.l + b.r = b.l + a.r := Iff.rfl

end Bal

/-- `peq`: a tie of pairs by the identity of masses of its components. -/
syntax (name := peqTac) "peq" (" [" Qpp.Qeq.farkasArg,* "]")? : tactic

macro_rules
  | `(tactic| peq) => `(tactic| (try simp only [Bal.Tie, Bal.add_l, Bal.add_r, Bal.mul_l, Bal.mul_r, Bal.swap_l,
      Bal.swap_r, Bal.of_l, Bal.of_r, Bal.level_l, Bal.level_r] at *) <;> qeq)
  | `(tactic| peq [$args,*]) => `(tactic| (try simp only [Bal.Tie, Bal.add_l, Bal.add_r, Bal.mul_l, Bal.mul_r,
      Bal.swap_l, Bal.swap_r, Bal.of_l, Bal.of_r, Bal.level_l, Bal.level_r] at *) <;> qeq [$args,*])

/-- `pfarkas [..]`: an inequality of pairs by a Farkas certificate on the masses of its components. -/
syntax (name := pfarkasTac) "pfarkas" (" [" Qpp.Qeq.farkasArg,* "]")? : tactic

macro_rules
  | `(tactic| pfarkas) => `(tactic| (try simp only [Bal.le_def, Bal.lt_def, Bal.tie_def, Bal.add_l, Bal.add_r,
      Bal.mul_l, Bal.mul_r, Bal.swap_l, Bal.swap_r, Bal.of_l, Bal.of_r, Bal.level_l, Bal.level_r] at *) <;> farkas)
  | `(tactic| pfarkas [$args,*]) => `(tactic| (try simp only [Bal.le_def, Bal.lt_def, Bal.tie_def, Bal.add_l,
      Bal.add_r, Bal.mul_l, Bal.mul_r, Bal.swap_l, Bal.swap_r, Bal.of_l, Bal.of_r, Bal.level_l, Bal.level_r] at *)
      <;> farkas [$args,*])

namespace Bal

open Mass

/-- A pair is at least `0` exactly when its right mass is at most its left one. -/
theorem nonneg_iff {a : Bal Mass} : level ≤ a ↔ a.r ≤ a.l := by
  rw [le_def]; simp only [level_l, level_r]
  constructor
  · rintro (h | ⟨z, hz⟩)
    · exact Or.inl (add_left_cancel (z := 1) (by rw [h, add_comm]))
    · exact Or.inr ⟨z, add_left_cancel (z := 1) (by rw [add_comm 1 a.l, hz]; qeq)⟩
  · rintro (h | ⟨z, hz⟩)
    · exact Or.inl (by rw [h, add_comm])
    · exact Or.inr ⟨z, by rw [hz]; qeq⟩

/-- A pair is `0` or its left mass is the right one plus a mass `c`, or the other way round. -/
theorem cases (a : Bal Mass) : a.l = a.r ∨ (∃ c, a.l = a.r + c) ∨ (∃ c, a.r = a.l + c) := by
  rcases trichotomy a.r a.l with ⟨c, h⟩ | h | ⟨c, h⟩
  · exact Or.inr (Or.inl ⟨c, h⟩)
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr ⟨c, h⟩)

/-- A square is at least `0`. -/
theorem sq_nonneg (a : Bal Mass) : level ≤ a * a := by
  rw [nonneg_iff]; simp only [mul_l, mul_r]
  rcases cases a with h | ⟨c, h⟩ | ⟨c, h⟩
  · exact Or.inl (by rw [h])
  · exact Or.inr ⟨c * c, by rw [h]; qeq⟩
  · exact Or.inr ⟨c * c, by rw [h]; qeq⟩

/-- A product of pairs at least `0` is at least `0`. -/
theorem mul_nonneg {a b : Bal Mass} (ha : level ≤ a) (hb : level ≤ b) : level ≤ a * b := by
  rw [nonneg_iff] at *; simp only [mul_l, mul_r]
  rcases ha with ha | ⟨c, ha⟩ <;> rcases hb with hb | ⟨d, hb⟩
  · exact Or.inl (by rw [ha, hb])
  · exact Or.inl (by rw [ha, hb] <;> qeq)
  · exact Or.inl (by rw [ha, hb] <;> qeq)
  · exact Or.inr ⟨c * d, by rw [ha, hb] <;> qeq⟩

/-- `a ≤ b` gives `0 ≤ b - a`. -/
theorem sub_nonneg {a b : Bal Mass} (h : a ≤ b) : level ≤ b + swap a := by
  pfarkas [h]

/-- `a < b` gives `0 ≤ b - a`. -/
theorem sub_nonneg_of_lt {a b : Bal Mass} (h : a < b) : level ≤ b + swap a := by
  pfarkas [h]

/-- Two inequalities give the tie. -/
theorem tie_of_le_le {a b : Bal Mass} (h1 : a ≤ b) (h2 : b ≤ a) : a.Tie b := by
  rw [le_def] at h1 h2; rw [tie_def]; exact Mass.le_antisymm h1 h2

/-- Not above is at most. -/
theorem le_of_not_lt {a b : Bal Mass} (h : ¬ b < a) : a ≤ b := by
  rw [le_def]; rw [lt_def] at h; exact Mass.le_of_not_lt h

/-- Not at most is above. -/
theorem lt_of_not_le {a b : Bal Mass} (h : ¬ a ≤ b) : b < a := by
  rcases Mass.bal_trichotomy a b with h' | h' | h'
  · exact absurd (Or.inr h') h
  · exact absurd (Or.inl h') h
  · exact h'

/-- A tie times a pair. -/
theorem tie_mul {a b : Bal Mass} (h : a.Tie b) (t : Bal Mass) : (a * t).Tie (b * t) := Mass.bal_mul_tie_left t h

/-- `0 < x` for a mass `x`. -/
theorem of_pos (x : Mass) : level < of x := by
  rw [lt_def]; simp only [level_l, level_r, of_l, of_r]; exact ⟨x, by qeq⟩

/-- `0 ≤ n` for a numeral of Lean. -/
theorem nat_nonneg : ∀ n : Nat, level ≤ Bal.nat n
  | 0 => Or.inl rfl
  | _ + 1 => Or.inr (of_pos _)

/-- The larger of two pairs is at least each, and tied to one of them. -/
theorem IsMax.ge_left {m a b : Bal Mass} (h : IsMax m a b) : a ≤ m := by
  rcases h with ⟨rfl, _⟩ | ⟨rfl, h⟩
  · exact Or.inl rfl
  · exact h

theorem IsMax.ge_right {m a b : Bal Mass} (h : IsMax m a b) : b ≤ m := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, _⟩
  · exact h
  · exact Or.inl rfl

theorem IsMax.cases {m a b : Bal Mass} (h : IsMax m a b) : (m.Tie a ∧ b ≤ a) ∨ (m.Tie b ∧ a ≤ b) := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr ⟨rfl, h⟩

/-- The smaller of two pairs is at most each, and tied to one of them. -/
theorem IsMin.le_left {m a b : Bal Mass} (h : IsMin m a b) : m ≤ a := by
  rcases h with ⟨rfl, _⟩ | ⟨rfl, h⟩
  · exact Or.inl rfl
  · exact h

theorem IsMin.le_right {m a b : Bal Mass} (h : IsMin m a b) : m ≤ b := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, _⟩
  · exact h
  · exact Or.inl rfl

theorem IsMin.cases {m a b : Bal Mass} (h : IsMin m a b) : (m.Tie a ∧ a ≤ b) ∨ (m.Tie b ∧ b ≤ a) := by
  rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr ⟨rfl, h⟩

theorem nat_zero : Bal.nat 0 = level := rfl

/-- The successor of a count, read as a pair. -/
theorem ofCount_succ (n : Count) : (of (Mass.ofCount (Count.succ n))).Tie (of (Mass.ofCount n) + of 1) := by
  have h := Mass.ofCount_succ n
  peq [h]

/-- `n + 1` read as a pair. -/
theorem nat_succ : ∀ n : Nat, (Bal.nat (n + 1)).Tie (Bal.nat n + of 1)
  | 0 => by show (of 1).Tie (level + of 1); peq
  | n + 1 => by
    show (of (Mass.ofCount (Count.succ (Count.ofNatSucc n)))).Tie (of (Mass.ofCount (Count.ofNatSucc n)) + of 1)
    have h := Mass.ofCount_succ (Count.ofNatSucc n)
    peq [h]

/-! Powers with a variable exponent, and a positive factor. -/

/-- A pair above `0` is its right mass plus a mass. -/
theorem pos_iff {a : Bal Mass} : level < a ↔ ∃ c, a.l = a.r + c := by
  rw [lt_def]; simp only [level_l, level_r]
  constructor
  · rintro ⟨z, hz⟩; exact ⟨z, add_left_cancel (z := 1) (by rw [add_comm 1 a.l, hz]; qeq)⟩
  · rintro ⟨z, hz⟩; exact ⟨z, by rw [hz]; qeq⟩

/-- A product of pairs above `0` is above `0`. -/
theorem mul_pos {a b : Bal Mass} (ha : level < a) (hb : level < b) : level < a * b := by
  rw [pos_iff] at *; simp only [mul_l, mul_r]
  obtain ⟨c, ha⟩ := ha
  obtain ⟨d, hb⟩ := hb
  exact ⟨c * d, by rw [ha, hb]; qeq⟩

/-- `a < b` gives `0 < b - a`. -/
theorem sub_pos {a b : Bal Mass} (h : a < b) : level < b + swap a := by
  pfarkas [h]

theorem pow_nonneg {a : Bal Mass} (h : level ≤ a) : ∀ n : Nat, level ≤ a ^ n
  | 0 => Or.inr (of_pos 1)
  | n + 1 => mul_nonneg (pow_nonneg h n) h

theorem pow_pos {a : Bal Mass} (h : level < a) : ∀ n : Nat, level < a ^ n
  | 0 => of_pos 1
  | n + 1 => mul_pos (pow_pos h n) h

/-- Powers keep the order of pairs at least `0`. -/
theorem pow_le_pow_left {a b : Bal Mass} (h0 : level ≤ a) (h : a ≤ b) : ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => Or.inl rfl
  | n + 1 => by
    have ih := pow_le_pow_left h0 h n
    have hb0 : level ≤ b := by pfarkas [h0, h]
    have h1 := mul_nonneg (pow_nonneg hb0 n) (sub_nonneg h)
    have h2 := mul_nonneg h0 (sub_nonneg ih)
    show a ^ n * a ≤ b ^ n * b
    pfarkas [h1, h2]

theorem pow_lt_pow_left {a b : Bal Mass} (h0 : level ≤ a) (h : a < b) (n : Nat) : a ^ (n + 1) < b ^ (n + 1) := by
  have hb : level < b := by pfarkas [h0, h]
  have h1 := mul_pos (pow_pos hb n) (sub_pos h)
  have h2 := mul_nonneg h0 (sub_nonneg (pow_le_pow_left h0 (Or.inr h) n))
  show a ^ n * a < b ^ n * b
  pfarkas [h1, h2]

theorem _root_.Qpp.Count.toNat_eq_succ (j : Count) : ∃ k, j.toNat = k + 1 := by
  cases j with
  | one => exact ⟨0, rfl⟩
  | succ n => exact ⟨n.toNat, rfl⟩

/-- `pow[j]`: `a ≤ b` from `a ^ j ≤ b ^ j` and `0 ≤ b`. -/
theorem le_of_pow_le_pow {a b : Bal Mass} (hb : level ≤ b) (j : Count)
    (h : a ^ j.toNat ≤ b ^ j.toNat) : a ≤ b := by
  refine le_of_not_lt (fun hlt => ?_)
  obtain ⟨k, hk⟩ := Count.toNat_eq_succ j
  rw [hk] at h
  have h' := pow_lt_pow_left hb hlt k
  exact absurd (show (level : Bal Mass) < level by pfarkas [h, h']) (Mass.bal_lt_irrefl _)

/-- `pow[j]`: `a = 0` from `a ^ j = 0`, `a` at least `0`. -/
theorem tie_zero_of_pow {a : Bal Mass} (ha : level ≤ a) (j : Count) (h : (a ^ j.toNat).Tie level) :
    a.Tie level := by
  rcases ha with ha | ha
  · peq [ha]
  · obtain ⟨k, hk⟩ := Count.toNat_eq_succ j
    rw [hk] at h
    have h' := pow_pos ha (k + 1)
    exact absurd (show (level : Bal Mass) < level by pfarkas [h, h']) (Mass.bal_lt_irrefl _)

/-- `pow_tie`: tied bases, tied powers. -/
theorem pow_tie {a b : Bal Mass} (h : a.Tie b) : ∀ n : Nat, (a ^ n).Tie (b ^ n)
  | 0 => rfl
  | n + 1 => by
    have ih := pow_tie h n
    have h1 := tie_mul ih a
    have h2 := tie_mul h (b ^ n)
    show (a ^ n * a).Tie (b ^ n * b)
    peq [h1, h2]

/-- `div[c]`: a factor above `0` cancels. -/
theorem nonneg_of_mul_nonneg {c t : Bal Mass} (hc : level < c) (h : level ≤ c * t) : level ≤ t := by
  refine le_of_not_lt (fun ht => ?_)
  have h' := mul_pos hc (sub_pos ht)
  exact absurd (show (level : Bal Mass) < level by pfarkas [h, h']) (Mass.bal_lt_irrefl _)

theorem nonpos_of_mul_nonpos {c t : Bal Mass} (hc : level < c) (h : c * t ≤ level) : t ≤ level := by
  refine le_of_not_lt (fun ht => ?_)
  have h' := mul_pos hc (sub_pos ht)
  exact absurd (show (level : Bal Mass) < level by pfarkas [h, h']) (Mass.bal_lt_irrefl _)

theorem tie_zero_of_mul {c t : Bal Mass} (hc : level < c) (h : (c * t).Tie level) : t.Tie level :=
  tie_of_le_le (nonpos_of_mul_nonpos hc (by pfarkas [h])) (nonneg_of_mul_nonneg hc (by pfarkas [h.symm]))

/-! The first and the last term of a sum (`ind`: the sums at the least bound and at a successor). -/

theorem sumTo_one' {β : Type} [Add β] (f : Count → β) : sumTo f 1 = f 1 := rfl
theorem sumTo_succ' {β : Type} [Add β] (f : Count → β) (n : Count) :
    sumTo f (Count.succ n) = sumTo f n + f (Count.succ n) := rfl
theorem sumN_zero' {β : Type} [Add β] (z : β) (f : Count → β) : sumN z f 0 = z := rfl
theorem sumN_succ' {β : Type} [Add β] (z : β) (f : Count → β) (n : Nat) :
    sumN z f (n + 1) = sumN z f n + f (Count.ofNatSucc n) := rfl
theorem sumBelow_one' {β : Type} [Add β] (z : β) (f : Nat → β) : sumBelow z f (0 + 1) = z + f 0 := rfl
theorem sumBelow_succ' {β : Type} [Add β] (z : β) (f : Nat → β) (n : Nat) :
    sumBelow z f (n + 1 + 1) = sumBelow z f (n + 1) + f (n + 1) := rfl

/-! Sums of pairs, term by term: a tie or an inequality of every term is one of the sums. -/

theorem sumTo_tie {f g : Count → Bal Mass} (h : ∀ i, (f i).Tie (g i)) (n : Count) : (sumTo f n).Tie (sumTo g n) := by
  induction n using Count.ind with
  | h1 => exact h 1
  | hs n ih => have hn := h (.succ n); show (sumTo f n + f (.succ n)).Tie (sumTo g n + g (.succ n)); peq [ih, hn]

theorem sumTo_le {f g : Count → Bal Mass} (h : ∀ i, f i ≤ g i) (n : Count) : sumTo f n ≤ sumTo g n := by
  induction n using Count.ind with
  | h1 => exact h 1
  | hs n ih => have hn := h (.succ n); show sumTo f n + f (.succ n) ≤ sumTo g n + g (.succ n); pfarkas [ih, hn]

theorem sumTo_nonneg {f : Count → Bal Mass} (h : ∀ i, level ≤ f i) (n : Count) : level ≤ sumTo f n := by
  induction n using Count.ind with
  | h1 => exact h 1
  | hs n ih => have hn := h (.succ n); show level ≤ sumTo f n + f (.succ n); pfarkas [ih, hn]

theorem sumTo_nonpos {f : Count → Bal Mass} (h : ∀ i, f i ≤ level) (n : Count) : sumTo f n ≤ level := by
  induction n using Count.ind with
  | h1 => exact h 1
  | hs n ih => have hn := h (.succ n); show sumTo f n + f (.succ n) ≤ level; pfarkas [ih, hn]

theorem sumTo_tie_level {f : Count → Bal Mass} (h : ∀ i, (f i).Tie level) (n : Count) : (sumTo f n).Tie level := by
  induction n using Count.ind with
  | h1 => exact h 1
  | hs n ih => have hn := h (.succ n); show (sumTo f n + f (.succ n)).Tie level; peq [ih, hn]

/-! Sums of pairs over `1..n`, term by term, from a relation of the terms up to `n` only. -/

theorem le_succ_of_le {i n : Count} (h : i ≤ n) : i ≤ Count.succ n :=
  Or.inr (Count.lt_of_le_of_lt h (Count.lt_succ n))

theorem sumTo_tie_upto {f g : Count → Bal Mass} (n : Count) :
    (∀ i, i ≤ n → (f i).Tie (g i)) → (sumTo f n).Tie (sumTo g n) := by
  induction n using Count.ind with
  | h1 => intro h; exact h 1 (Or.inl rfl)
  | hs n ih =>
    intro h
    have ih' := ih (fun i hi => h i (le_succ_of_le hi)); have hn := h (.succ n) (Or.inl rfl)
    show (sumTo f n + f (.succ n)).Tie (sumTo g n + g (.succ n)); peq [ih', hn]

theorem sumTo_le_upto {f g : Count → Bal Mass} (n : Count) :
    (∀ i, i ≤ n → f i ≤ g i) → sumTo f n ≤ sumTo g n := by
  induction n using Count.ind with
  | h1 => intro h; exact h 1 (Or.inl rfl)
  | hs n ih =>
    intro h
    have ih' := ih (fun i hi => h i (le_succ_of_le hi)); have hn := h (.succ n) (Or.inl rfl)
    show sumTo f n + f (.succ n) ≤ sumTo g n + g (.succ n); pfarkas [ih', hn]

theorem sumTo_nonneg_upto {f : Count → Bal Mass} (n : Count) :
    (∀ i, i ≤ n → level ≤ f i) → level ≤ sumTo f n := by
  induction n using Count.ind with
  | h1 => intro h; exact h 1 (Or.inl rfl)
  | hs n ih =>
    intro h
    have ih' := ih (fun i hi => h i (le_succ_of_le hi)); have hn := h (.succ n) (Or.inl rfl)
    show level ≤ sumTo f n + f (.succ n); pfarkas [ih', hn]

theorem sumTo_nonpos_upto {f : Count → Bal Mass} (n : Count) :
    (∀ i, i ≤ n → f i ≤ level) → sumTo f n ≤ level := by
  induction n using Count.ind with
  | h1 => intro h; exact h 1 (Or.inl rfl)
  | hs n ih =>
    intro h
    have ih' := ih (fun i hi => h i (le_succ_of_le hi)); have hn := h (.succ n) (Or.inl rfl)
    show sumTo f n + f (.succ n) ≤ level; pfarkas [ih', hn]

theorem sumTo_tie_level_upto {f : Count → Bal Mass} (n : Count) :
    (∀ i, i ≤ n → (f i).Tie level) → (sumTo f n).Tie level := by
  induction n using Count.ind with
  | h1 => intro h; exact h 1 (Or.inl rfl)
  | hs n ih =>
    intro h
    have ih' := ih (fun i hi => h i (le_succ_of_le hi)); have hn := h (.succ n) (Or.inl rfl)
    show (sumTo f n + f (.succ n)).Tie level; peq [ih', hn]

theorem sumN_tie {f g : Count → Bal Mass} (h : ∀ i, (f i).Tie (g i)) :
    ∀ n, (sumN level f n).Tie (sumN level g n)
  | 0 => rfl
  | n + 1 => by
    have ih := sumN_tie h n; have hn := h (Count.ofNatSucc n)
    show (sumN level f n + f (Count.ofNatSucc n)).Tie (sumN level g n + g (Count.ofNatSucc n)); peq [ih, hn]

theorem sumN_le {f g : Count → Bal Mass} (h : ∀ i, f i ≤ g i) : ∀ n, sumN level f n ≤ sumN level g n
  | 0 => Or.inl rfl
  | n + 1 => by
    have ih := sumN_le h n; have hn := h (Count.ofNatSucc n)
    show sumN level f n + f (Count.ofNatSucc n) ≤ sumN level g n + g (Count.ofNatSucc n); pfarkas [ih, hn]

theorem sumN_nonneg {f : Count → Bal Mass} (h : ∀ i, level ≤ f i) : ∀ n, level ≤ sumN level f n
  | 0 => Or.inl rfl
  | n + 1 => by
    have ih := sumN_nonneg h n; have hn := h (Count.ofNatSucc n)
    show level ≤ sumN level f n + f (Count.ofNatSucc n); pfarkas [ih, hn]

theorem sumN_nonpos {f : Count → Bal Mass} (h : ∀ i, f i ≤ level) : ∀ n, sumN level f n ≤ level
  | 0 => Or.inl rfl
  | n + 1 => by
    have ih := sumN_nonpos h n; have hn := h (Count.ofNatSucc n)
    show sumN level f n + f (Count.ofNatSucc n) ≤ level; pfarkas [ih, hn]

theorem sumN_tie_level {f : Count → Bal Mass} (h : ∀ i, (f i).Tie level) : ∀ n, (sumN level f n).Tie level
  | 0 => rfl
  | n + 1 => by
    have ih := sumN_tie_level h n; have hn := h (Count.ofNatSucc n)
    show (sumN level f n + f (Count.ofNatSucc n)).Tie level; peq [ih, hn]

theorem sumBelow_tie {f g : Nat → Bal Mass} (h : ∀ i, (f i).Tie (g i)) :
    ∀ n, (sumBelow level f n).Tie (sumBelow level g n)
  | 0 => rfl
  | n + 1 => by
    have ih := sumBelow_tie h n; have hn := h n
    show (sumBelow level f n + f n).Tie (sumBelow level g n + g n); peq [ih, hn]

theorem sumBelow_le {f g : Nat → Bal Mass} (h : ∀ i, f i ≤ g i) : ∀ n, sumBelow level f n ≤ sumBelow level g n
  | 0 => Or.inl rfl
  | n + 1 => by
    have ih := sumBelow_le h n; have hn := h n
    show sumBelow level f n + f n ≤ sumBelow level g n + g n; pfarkas [ih, hn]

theorem sumBelow_nonneg {f : Nat → Bal Mass} (h : ∀ i, level ≤ f i) : ∀ n, level ≤ sumBelow level f n
  | 0 => Or.inl rfl
  | n + 1 => by
    have ih := sumBelow_nonneg h n; have hn := h n
    show level ≤ sumBelow level f n + f n; pfarkas [ih, hn]

theorem sumBelow_nonpos {f : Nat → Bal Mass} (h : ∀ i, f i ≤ level) : ∀ n, sumBelow level f n ≤ level
  | 0 => Or.inl rfl
  | n + 1 => by
    have ih := sumBelow_nonpos h n; have hn := h n
    show sumBelow level f n + f n ≤ level; pfarkas [ih, hn]

theorem sumBelow_tie_level {f : Nat → Bal Mass} (h : ∀ i, (f i).Tie level) : ∀ n, (sumBelow level f n).Tie level
  | 0 => rfl
  | n + 1 => by
    have ih := sumBelow_tie_level h n; have hn := h n
    show (sumBelow level f n + f n).Tie level; peq [ih, hn]

/-- The larger of two pairs exists. -/
theorem exists_isMax (a b : Bal Mass) : ∃ m, IsMax m a b := by
  rcases trichotomy (a.l + b.r) (b.l + a.r) with h | h | h
  · exact ⟨b, Or.inr ⟨rfl, Or.inr h⟩⟩
  · exact ⟨a, Or.inl ⟨rfl, Or.inl h.symm⟩⟩
  · exact ⟨a, Or.inl ⟨rfl, Or.inr h⟩⟩

end Bal

end Qpp
