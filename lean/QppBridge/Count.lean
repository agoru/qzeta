module

public import QppKernel.Words
public import QppBridge.Attr
public import Mathlib.Data.PNat.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Order.MinMax
public import Mathlib.Data.Nat.Choose.Basic

/-!
# The bridge of counts: `Count ≃ ℕ+` and `Count0 ≃ ℕ`

A count is read as the natural number of the same size (`Count.toNat`, in `Base`), and a count or absent as a natural
number with absent at `0` (`Count0.toNat`). Both readings are bijections (`Count.equivPNat`, `Count0.equivNat`), and
they carry every word of the kernel on counts to the word of Mathlib of the same name: the transport lemmas
(`qpp_bridge`). Each proof only connects the two sides; the laws of `ℕ` come from Mathlib.
-/

@[expose] public section

namespace Qpp

open Classical

/-! ## Counts -/

namespace Count

/-- The count of a positive natural number. -/
def ofPNat (n : ℕ+) : Count := ofNatSucc (n.natPred)

theorem toNat_ofPNat (n : ℕ+) : (ofPNat n).toNat = n := by
  rw [ofPNat, toNat_ofNatSucc]; exact PNat.natPred_add_one n

/-- The reading of a count as a positive natural number. -/
def toPNat (a : Count) : ℕ+ := ⟨a.toNat, toNat_pos a⟩

/-- `Count ≃ ℕ+`. -/
def equivPNat : Count ≃ ℕ+ where
  toFun := toPNat
  invFun := ofPNat
  left_inv a := toNat_inj (toNat_ofPNat (toPNat a))
  right_inv n := PNat.eq (toNat_ofPNat n)

theorem toNat_injective : Function.Injective toNat := fun _ _ h => toNat_inj h

@[qpp_bridge] theorem toNat_eq {a b : Count} : a = b ↔ a.toNat = b.toNat :=
  ⟨congrArg _, fun h => toNat_inj h⟩

@[qpp_bridge] theorem toNat_one' : (1 : Count).toNat = 1 := rfl

/-- A count read in `ℕ` is at least `1`: the hypothesis of a binder in `NN>=1` over Mathlib. -/
theorem one_le_toNat (a : Count) : 1 ≤ a.toNat := toNat_pos a

@[qpp_bridge] theorem toNat_ofNat (n : ℕ) : (no_index (OfNat.ofNat (n + 1)) : Count).toNat = n + 1 := toNat_ofNatSucc n

attribute [qpp_bridge] toNat_add toNat_mul toNat_pow

theorem toNat_succ' (a : Count) : (succ a).toNat = a.toNat + 1 := rfl

/-- The count of a natural number at least `1`; `1` at `0`. -/
def ofNat (n : ℕ) : Count := ofNatSucc (n - 1)

theorem toNat_ofNat_of_pos {n : ℕ} (h : 0 < n) : (ofNat n).toNat = n := by
  rw [ofNat, toNat_ofNatSucc]; omega

@[qpp_bridge] theorem toNat_lt {a b : Count} : a < b ↔ a.toNat < b.toNat := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [toNat_add]; have := toNat_pos c; omega
  · intro h
    refine ⟨ofNat (b.toNat - a.toNat), toNat_inj ?_⟩
    rw [toNat_add, toNat_ofNat_of_pos (by omega)]; omega

@[qpp_bridge] theorem toNat_le {a b : Count} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  show a = b ∨ a < b ↔ _
  rw [toNat_lt, toNat_eq]; omega

@[qpp_bridge] theorem toNat_powCount (a e : Count) : (a ^ e).toNat = a.toNat ^ e.toNat := by
  show (powCount a e).toNat = _
  induction e using ind with
  | h1 => exact (Nat.pow_one _).symm
  | hs e ih => rw [powCount, toNat_mul, ih, toNat_succ', Nat.pow_succ]

theorem le_iff (a b : Count) : a ≤ b ↔ a.toNat ≤ b.toNat := toNat_le

@[qpp_bridge] theorem toNat_min (a b : Count) : (min a b).toNat = min a.toNat b.toNat := by
  show (if a ≤ b then a else b).toNat = _
  split_ifs with h
  · rw [toNat_le] at h; exact (min_eq_left h).symm
  · rw [toNat_le] at h; exact (min_eq_right (by omega)).symm

@[qpp_bridge] theorem toNat_max (a b : Count) : (max a b).toNat = max a.toNat b.toNat := by
  show (if a ≤ b then b else a).toNat = _
  split_ifs with h
  · rw [toNat_le] at h; exact (max_eq_right h).symm
  · rw [toNat_le] at h; exact (max_eq_left (by omega)).symm

end Count

/-! ## Counts or absent -/

namespace Count0

/-- The reading of a count or absent as a natural number: absent is `0`. -/
def toNat : Count0 → ℕ
  | none => 0
  | some c => c.toNat

/-- The count or absent of a natural number: `0` is absent. -/
def ofNat : ℕ → Count0
  | 0 => 0
  | n + 1 => of (Count.ofNatSucc n)

@[qpp_bridge] theorem toNat_ofNat (n : ℕ) : (ofNat n).toNat = n := by
  cases n with
  | zero => rfl
  | succ n => exact Count.toNat_ofNatSucc n

theorem ofNat_toNat (x : Count0) : ofNat x.toNat = x := by
  cases x with
  | none => rfl
  | some c =>
    show ofNat c.toNat = some c
    obtain ⟨n, hn⟩ : ∃ n, c.toNat = n + 1 := ⟨c.toNat - 1, by have := Count.toNat_pos c; omega⟩
    rw [hn]; show some (Count.ofNatSucc n) = some c
    congr 1; exact Count.toNat_inj (by rw [Count.toNat_ofNatSucc, hn])

/-- `Count0 ≃ ℕ`. -/
def equivNat : Count0 ≃ ℕ where
  toFun := toNat
  invFun := ofNat
  left_inv := ofNat_toNat
  right_inv := toNat_ofNat

theorem toNat_injective : Function.Injective toNat := equivNat.injective

@[qpp_bridge] theorem toNat_eq {a b : Count0} : a = b ↔ a.toNat = b.toNat := toNat_injective.eq_iff.symm

@[qpp_bridge] theorem toNat_of (c : Count) : (of c).toNat = c.toNat := rfl
@[qpp_bridge] theorem toNat_zero : (0 : Count0).toNat = 0 := rfl
@[qpp_bridge] theorem toNat_one : (1 : Count0).toNat = 1 := rfl
@[qpp_bridge] theorem toNat_ofNat2 (n : ℕ) : (no_index (OfNat.ofNat (n + 2)) : Count0).toNat = n + 2 := by
  show (Count.ofNatSucc (n + 1)).toNat = _; rw [Count.toNat_ofNatSucc]

theorem toNat_pos_of {c : Count} : 0 < (of c).toNat := Count.toNat_pos c

/-! The index of a member of a family: a family over the kernel, `a : Count0 → X`, is read as the function of the
naturals `i ↦ a (ofNat i)`; at the reading of an index of the kernel the member is the member of the kernel. -/

attribute [qpp_bridge] ofNat_toNat

@[qpp_bridge] theorem ofNat_toNat_count (c : Count) : ofNat c.toNat = of c := by
  have h := ofNat_toNat (of c); rwa [toNat_of] at h

@[qpp_bridge] theorem ofNat_zero : ofNat 0 = 0 := rfl
@[qpp_bridge] theorem ofNat_one : ofNat 1 = 1 := rfl
@[qpp_bridge] theorem ofNat_ofNat2 (n : ℕ) : ofNat (no_index (OfNat.ofNat (n + 2))) = (OfNat.ofNat (n + 2) : Count0) :=
  rfl

@[qpp_bridge] theorem toNat_add (a b : Count0) : (a + b).toNat = a.toNat + b.toNat := by
  rcases a with _ | a <;> rcases b with _ | b
  · rfl
  · exact (Nat.zero_add _).symm
  · rfl
  · exact Count.toNat_add a b

/-- A member read at a sum of indices, `a_(j + 1)`: the index of the kernel is the sum of the indices. -/
@[qpp_bridge] theorem ofNat_add (m n : ℕ) : ofNat (m + n) = ofNat m + ofNat n := by
  apply toNat_injective; rw [toNat_add, toNat_ofNat, toNat_ofNat, toNat_ofNat]

@[qpp_bridge] theorem toNat_mul (a b : Count0) : (a * b).toNat = a.toNat * b.toNat := by
  rcases a with _ | a <;> rcases b with _ | b
  · rfl
  · exact (Nat.zero_mul _).symm
  · exact (Nat.mul_zero _).symm
  · exact Count.toNat_mul a b

@[qpp_bridge] theorem toNat_lt {a b : Count0} : a < b ↔ a.toNat < b.toNat := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [toNat_add, toNat_of]; have := Count.toNat_pos c; omega
  · intro h
    refine ⟨Count.ofNat (b.toNat - a.toNat), toNat_injective ?_⟩
    rw [toNat_add, toNat_of, Count.toNat_ofNat_of_pos (by omega)]; omega

@[qpp_bridge] theorem toNat_le {a b : Count0} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  show a = b ∨ a < b ↔ _
  rw [toNat_lt, toNat_eq]; omega

theorem toNat_powNat (a : Count0) (k : ℕ) : (powNat a k).toNat = a.toNat ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [powNat, toNat_mul, ih, Nat.pow_succ]

@[qpp_bridge] theorem toNat_npow (a : Count0) (k : ℕ) : (a ^ k).toNat = a.toNat ^ k := toNat_powNat a k

theorem toNat_powCount (a : Count0) (e : Count) : (powCount a e).toNat = a.toNat ^ e.toNat := by
  induction e using Count.ind with
  | h1 => exact (Nat.pow_one _).symm
  | hs e ih => rw [powCount, toNat_mul, ih, Count.toNat_succ', Nat.pow_succ]

@[qpp_bridge] theorem toNat_hpowCount (a : Count0) (e : Count) : (a ^ e).toNat = a.toNat ^ e.toNat :=
  toNat_powCount a e

@[qpp_bridge] theorem toNat_hpowCount0 (a e : Count0) : (a ^ e).toNat = a.toNat ^ e.toNat := by
  cases e with
  | none => rfl
  | some e => exact toNat_powCount a e

@[qpp_bridge] theorem toNat_min (a b : Count0) : (min a b).toNat = min a.toNat b.toNat := by
  show (if a ≤ b then a else b).toNat = _
  split_ifs with h
  · rw [toNat_le] at h; exact (min_eq_left h).symm
  · rw [toNat_le] at h; exact (min_eq_right (by omega)).symm

@[qpp_bridge] theorem toNat_max (a b : Count0) : (max a b).toNat = max a.toNat b.toNat := by
  show (if a ≤ b then b else a).toNat = _
  split_ifs with h
  · rw [toNat_le] at h; exact (max_eq_right h).symm
  · rw [toNat_le] at h; exact (max_eq_left (by omega)).symm

/-- The deficit of counts is the truncated difference, which is also `max (a - b) 0`. -/
@[qpp_bridge] theorem toNat_deficit (a b : Count0) : (Count0.deficit a b).toNat = max (a.toNat - b.toNat) 0 := by
  rw [max_eq_left (Nat.zero_le _)]
  unfold Count0.deficit
  split_ifs with h
  · have hc := Classical.choose_spec h
    have e := congrArg toNat hc
    rw [toNat_add, toNat_of] at e
    rw [toNat_of]; omega
  · rw [toNat_lt] at h; show 0 = _; omega

/-- A deficit read as a count (a line at `max(x - k, 0)`) is the count of the truncated difference. -/
@[qpp_bridge] theorem deficit_eq_ofNat (a b : Count0) : Count0.deficit a b = ofNat (max (a.toNat - b.toNat) 0) := by
  apply toNat_injective; rw [toNat_deficit, toNat_ofNat]

@[qpp_bridge] theorem toNat_iversonN (P : Prop) [Decidable P] : (iversonN P).toNat = if P then 1 else 0 := by
  unfold iversonN; split_ifs <;> rfl

end Count0

@[qpp_bridge] theorem Count0.toNat_ofCount (c : Count) : (Count0.of c).toNat = c.toNat := rfl

/-! ## A count plus a count or absent, a count to the power of a count or absent -/

@[qpp_bridge] theorem Count.toNat_add0 (c : Count) (j : Count0) : (c + j).toNat = c.toNat + j.toNat := by
  cases j with
  | none => rfl
  | some d => exact Count.toNat_add c d

@[qpp_bridge] theorem Count.toNat_add0' (j : Count0) (c : Count) : (j + c).toNat = j.toNat + c.toNat := by
  rw [Nat.add_comm]; exact Count.toNat_add0 c j

@[qpp_bridge] theorem Count.toNat_hpowCount0 (a : Count) (e : Count0) : (a ^ e).toNat = a.toNat ^ e.toNat := by
  cases e with
  | none => rfl
  | some e => exact Count.toNat_powCount a e

/-! ## Binomial coefficients: Pascal's rule read as `Nat.choose` -/

theorem Count.toNat_pred0 (k : Count) : (Count.pred0 k).toNat = k.toNat - 1 := by
  cases k with
  | one => rfl
  | succ c => show c.toNat = c.toNat + 1 - 1; omega

theorem Count.toNat_binom (c : Count) (k : Count0) : (Count.binom c k).toNat = Nat.choose c.toNat k.toNat := by
  induction c generalizing k with
  | one =>
    rcases k with _ | k
    · rfl
    · cases k with
      | one => rfl
      | succ k =>
        show 0 = Nat.choose 1 (k.toNat + 1)
        have := Count.toNat_pos k
        rw [Nat.choose_eq_zero_of_lt (by omega)]
  | succ c ih =>
    rcases k with _ | k
    · show 1 = Nat.choose _ 0; rw [Nat.choose_zero_right]
    · have e : Count.binom (Count.succ c) (Count0.of k) =
          Count.binom c (Count.pred0 k) + Count.binom c (Count0.of k) := by
        unfold Count0.of; rw [Count.binom]
      show (Count.binom (Count.succ c) (Count0.of k)).toNat = Nat.choose (c.toNat + 1) k.toNat
      rw [e, Count0.toNat_add, ih (Count.pred0 k), ih (Count0.of k), Count.toNat_pred0]
      obtain ⟨j, hj⟩ : ∃ j, k.toNat = j + 1 := ⟨k.toNat - 1, by have := Count.toNat_pos k; omega⟩
      show Nat.choose c.toNat (k.toNat - 1) + Nat.choose c.toNat k.toNat = _
      rw [hj, Nat.choose_succ_succ, Nat.add_sub_cancel]

@[qpp_bridge] theorem Count0.toNat_binom (n k : Count0) :
    (Count0.binom n k).toNat = Nat.choose n.toNat k.toNat := by
  rcases n with _ | c
  · rcases k with _ | k
    · rfl
    · show 0 = Nat.choose 0 k.toNat
      rw [Nat.choose_eq_zero_of_lt (Count.toNat_pos k)]
  · exact Count.toNat_binom c k

end Qpp
