module

public import QppBridge.Mass
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Pi.Interval
public import Mathlib.Data.Fin.Tuple.Finset
public import Mathlib.Order.Interval.Finset.Nat

/-!
# The bridge of indices, tuples and sums

The indices `Idx n` (the counts `1, ..., n`) are read as `Fin n` (`Idx.equivFin`: the count `i` is `i - 1`), and a
tuple `u : Idx n → X` as the function `Idx.map φ u : Fin n → Y` of the readings `φ` of its entries. A sum over the
indices, over a range or over the lattice points of a box is read as the `Finset.sum` that the Mathlib reading prints:
over `Finset.univ`, over `Finset.Icc a b`, over `Finset.Icc 0 b` of `Fin n → ℕ`. The same for products. The lemmas
are stated for any reading that carries `+` to `+` (or `*` to `*`), and then for the readings of masses and counts.
-/

@[expose] public section

namespace Qpp

open Classical Finset

/-! ## Indices -/

namespace Idx

theorem toNat_le {n : Count0} (i : Idx n) : i.1.toNat ≤ n.toNat := by
  have := Count0.toNat_le.mp i.2; rwa [Count0.toNat_of] at this

/-- The index `i` as `i - 1 : Fin n`. -/
def toFin {n : Count0} (i : Idx n) : Fin n.toNat :=
  ⟨i.1.toNat - 1, by have := i.toNat_le; have := Count.toNat_pos i.1; omega⟩

theorem of_le_of_lt {n : Count0} {j : ℕ} (h : j < n.toNat) : Count0.of (Count.ofNatSucc j) ≤ n := by
  rw [Count0.toNat_le, Count0.toNat_of, Count.toNat_ofNatSucc]; omega

/-- The index of `j : Fin n`: the count `j + 1`. -/
def ofFin {n : Count0} (j : Fin n.toNat) : Idx n := ⟨Count.ofNatSucc j.1, of_le_of_lt j.2⟩

@[qpp_bridge] theorem toFin_ofFin {n : Count0} (j : Fin n.toNat) : toFin (ofFin j) = j := by
  ext; simp [toFin, ofFin, Count.toNat_ofNatSucc]

@[qpp_bridge] theorem ofFin_toFin {n : Count0} (i : Idx n) : ofFin (toFin i) = i := by
  apply Subtype.ext; apply Count.toNat_inj
  simp only [ofFin, toFin, Count.toNat_ofNatSucc]; have := Count.toNat_pos i.1; omega

/-- `Idx n ≃ Fin n`. -/
def equivFin (n : Count0) : Idx n ≃ Fin n.toNat where
  toFun := toFin
  invFun := ofFin
  left_inv := ofFin_toFin
  right_inv := toFin_ofFin

@[qpp_bridge] theorem forall_iff {n : Count0} {P : Idx n → Prop} : (∀ i, P i) ↔ ∀ j : Fin n.toNat, P (ofFin j) :=
  ⟨fun h j => h _, fun h i => by rw [← ofFin_toFin i]; exact h _⟩

@[qpp_bridge] theorem exists_iff {n : Count0} {P : Idx n → Prop} : (∃ i, P i) ↔ ∃ j : Fin n.toNat, P (ofFin j) :=
  ⟨fun ⟨i, h⟩ => ⟨toFin i, by rwa [ofFin_toFin]⟩, fun ⟨j, h⟩ => ⟨_, h⟩⟩

theorem toNat_ofFin {n : Count0} (j : Fin n.toNat) : (ofFin j).1.toNat = j.1 + 1 := Count.toNat_ofNatSucc j.1

@[qpp_bridge] theorem ofFin_eq {n : Count0} {j j' : Fin n.toNat} : ofFin j = ofFin j' ↔ j = j' :=
  (equivFin n).symm.injective.eq_iff

@[qpp_bridge] theorem ofFin_lt {n : Count0} {j j' : Fin n.toNat} : ofFin j < ofFin j' ↔ j < j' := by
  show (ofFin j).1 < (ofFin j').1 ↔ _
  rw [Count.toNat_lt, toNat_ofFin, toNat_ofFin, Fin.lt_def]; omega

@[qpp_bridge] theorem ofFin_le {n : Count0} {j j' : Fin n.toNat} : ofFin j ≤ ofFin j' ↔ j ≤ j' := by
  show (ofFin j).1 ≤ (ofFin j').1 ↔ _
  rw [Count.toNat_le, toNat_ofFin, toNat_ofFin, Fin.le_iff_val_le_val]; omega

/-! An index compared as the count it is (two indices of two ranges, an index and a count): the count of `j : Fin n`
is `j + 1`. -/

attribute [qpp_bridge] toNat_ofFin

/-- The reading of a tuple: the readings of its entries, on `Fin n`. -/
def map {n : Count0} {X Y : Type} (φ : X → Y) (u : Idx n → X) : Fin n.toNat → Y := fun j => φ (u (ofFin j))

@[qpp_bridge] theorem map_apply {n : Count0} {X Y : Type} (φ : X → Y) (u : Idx n → X) (j : Fin n.toNat) :
    map φ u j = φ (u (ofFin j)) := rfl

/-- The tuple of a function on `Fin n`, by the inverse `ψ` of a reading. -/
def unmap {n : Count0} {X Y : Type} (ψ : Y → X) (v : Fin n.toNat → Y) : Idx n → X := fun i => ψ (v (toFin i))

@[qpp_bridge] theorem unmap_apply {n : Count0} {X Y : Type} (ψ : Y → X) (v : Fin n.toNat → Y) (i : Idx n) :
    unmap ψ v i = ψ (v (toFin i)) := rfl

theorem extend_ofNatSucc {β : Type} {n : Count0} (z : β) (f : Idx n → β) (j : Fin n.toNat) :
    Idx.extend z f (Count.ofNatSucc j.1) = f (ofFin j) := by
  unfold Idx.extend; simp only [of_le_of_lt j.2, dite_true]; rfl

end Idx

/-! ## Sums and products over the counts `1, ..., c` and over the indices -/

section Maps

variable {β γ : Type}

theorem ofNatSucc_toNat (c : Count) : Count.ofNatSucc c.toNat = Count.succ c :=
  Count.toNat_inj (by rw [Count.toNat_ofNatSucc, Count.toNat_succ'])

theorem map_sumTo [Add β] [AddCommMonoid γ] (φ : β → γ) (hφ : ∀ a b, φ (a + b) = φ a + φ b)
    (g : Count → β) (c : Count) : φ (sumTo g c) = ∑ j : Fin c.toNat, φ (g (Count.ofNatSucc j.1)) := by
  induction c using Count.ind with
  | h1 => show φ (g 1) = ∑ j : Fin 1, _; rw [Fin.sum_univ_one]; rfl
  | hs c ih =>
    show φ (sumTo g c + g (Count.succ c)) = ∑ j : Fin (c.toNat + 1), _
    rw [hφ, ih, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ofNatSucc_toNat]

theorem map_prodTo [Mul β] [CommMonoid γ] (φ : β → γ) (hφ : ∀ a b, φ (a * b) = φ a * φ b)
    (g : Count → β) (c : Count) : φ (prodTo g c) = ∏ j : Fin c.toNat, φ (g (Count.ofNatSucc j.1)) := by
  induction c using Count.ind with
  | h1 => show φ (g 1) = ∏ j : Fin 1, _; rw [Fin.prod_univ_one]; rfl
  | hs c ih =>
    show φ (prodTo g c * g (Count.succ c)) = ∏ j : Fin (c.toNat + 1), _
    rw [hφ, ih, Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ofNatSucc_toNat]

theorem map_idxSum [Add β] [Zero β] [AddCommMonoid γ] (φ : β → γ) (hφ : ∀ a b, φ (a + b) = φ a + φ b)
    (h0 : φ 0 = 0) (n : Count0) (f : Idx n → β) : φ (Idx.sum n f) = ∑ j : Fin n.toNat, φ (f (Idx.ofFin j)) := by
  cases n with
  | none => exact h0
  | some c =>
    show φ (sumTo (Idx.extend 0 f) c) = _
    rw [map_sumTo φ hφ]
    exact Finset.sum_congr rfl fun j _ => congrArg φ (Idx.extend_ofNatSucc _ f j)

theorem map_idxProd [Mul β] [OfNat β 1] [CommMonoid γ] (φ : β → γ) (hφ : ∀ a b, φ (a * b) = φ a * φ b)
    (h1 : φ 1 = 1) (n : Count0) (f : Idx n → β) : φ (Idx.prod n f) = ∏ j : Fin n.toNat, φ (f (Idx.ofFin j)) := by
  cases n with
  | none => exact h1
  | some c =>
    show φ (prodTo (Idx.extend 1 f) c) = _
    rw [map_prodTo φ hφ]
    exact Finset.prod_congr rfl fun j _ => congrArg φ (Idx.extend_ofNatSucc _ f j)

/-- `Σ_{v=0}^{b} g v` as a sum over `Finset.Icc 0 b`. -/
theorem map_upTo [Add β] [AddCommMonoid γ] (φ : β → γ) (hφ : ∀ a b, φ (a + b) = φ a + φ b)
    (b : Count0) (g : Count0 → β) : φ (upTo b g) = ∑ v ∈ Icc 0 b.toNat, φ (g (Count0.ofNat v)) := by
  cases b with
  | none => show φ (g 0) = ∑ v ∈ Icc 0 0, _; rw [Icc_self, sum_singleton]; rfl
  | some c =>
    show φ (g 0 + sumTo _ c) = ∑ v ∈ Icc 0 c.toNat, _
    rw [hφ, map_sumTo φ hφ, ← Nat.range_succ_eq_Icc_zero, sum_range_succ', add_comm]
    congr 1
    exact Fin.sum_univ_eq_sum_range (fun j => φ (g (Count0.of (Count.ofNatSucc j)))) _

theorem map_upToProd [Mul β] [CommMonoid γ] (φ : β → γ) (hφ : ∀ a b, φ (a * b) = φ a * φ b)
    (b : Count0) (g : Count0 → β) : φ (upToProd b g) = ∏ v ∈ Icc 0 b.toNat, φ (g (Count0.ofNat v)) := by
  cases b with
  | none => show φ (g 0) = ∏ v ∈ Icc 0 0, _; rw [Icc_self, prod_singleton]; rfl
  | some c =>
    show φ (g 0 * prodTo _ c) = ∏ v ∈ Icc 0 c.toNat, _
    rw [hφ, map_prodTo φ hφ, ← Nat.range_succ_eq_Icc_zero, prod_range_succ', mul_comm]
    congr 1
    exact Fin.prod_univ_eq_prod_range (fun j => φ (g (Count0.of (Count.ofNatSucc j)))) _

theorem map_rangeSum [Add β] [Zero β] [AddCommMonoid γ] (φ : β → γ) (hφ : ∀ a b, φ (a + b) = φ a + φ b)
    (h0 : φ 0 = 0) (a b : Count0) (f : Count0 → β) :
    φ (rangeSum a b f) = ∑ v ∈ Icc a.toNat b.toNat, φ (f (Count0.ofNat v)) := by
  unfold rangeSum
  rw [map_upTo φ hφ]
  have e : ∀ v ∈ Icc 0 b.toNat, φ (if a ≤ Count0.ofNat v then f (Count0.ofNat v) else 0) =
      if a.toNat ≤ v then φ (f (Count0.ofNat v)) else 0 := fun v _ => by
    rw [Count0.toNat_le, Count0.toNat_ofNat]; split_ifs <;> simp [h0]
  rw [sum_congr rfl e, ← sum_filter]
  congr 1
  ext v; simp only [mem_filter, mem_Icc]; omega

theorem map_rangeProd [Mul β] [OfNat β 1] [CommMonoid γ] (φ : β → γ) (hφ : ∀ a b, φ (a * b) = φ a * φ b)
    (h1 : φ 1 = 1) (a b : Count0) (f : Count0 → β) :
    φ (rangeProd a b f) = ∏ v ∈ Icc a.toNat b.toNat, φ (f (Count0.ofNat v)) := by
  unfold rangeProd
  rw [map_upToProd φ hφ]
  have e : ∀ v ∈ Icc 0 b.toNat, φ (if a ≤ Count0.ofNat v then f (Count0.ofNat v) else 1) =
      if a.toNat ≤ v then φ (f (Count0.ofNat v)) else 1 := fun v _ => by
    rw [Count0.toNat_le, Count0.toNat_ofNat]; split_ifs <;> simp [h1]
  rw [prod_congr rfl e, ← prod_filter]
  congr 1
  ext v; simp only [mem_filter, mem_Icc]; omega

end Maps

/-! ## The readings of masses and counts -/

@[qpp_bridge] theorem Mass0.toRat_idxSum (n : Count0) (f : Idx n → Mass0) :
    (Idx.sum n f).toRat = ∑ j : Fin n.toNat, (f (Idx.ofFin j)).toRat :=
  map_idxSum _ Mass0.toRat_add Mass0.toRat_zero n f

@[qpp_bridge] theorem Count0.toNat_idxSum (n : Count0) (f : Idx n → Count0) :
    (Idx.sum n f).toNat = ∑ j : Fin n.toNat, (f (Idx.ofFin j)).toNat :=
  map_idxSum _ Count0.toNat_add Count0.toNat_zero n f

/-- A sum of counts as the count of the sum of its readings: the form that the Mathlib reading gives to a sum of counts
at which a function of counts is read (a line at the count of a set). Not in the simp set `qpp_bridge`, which reads a
sum through `toNat`; the transfer of a statement with such an argument rewrites by it. -/
theorem Count0.idxSum_eq_ofNat (n : Count0) (f : Idx n → Count0) :
    Idx.sum n f = Count0.ofNat (∑ j : Fin n.toNat, (f (Idx.ofFin j)).toNat) := by
  rw [← Count0.toNat_idxSum, Count0.ofNat_toNat]

@[qpp_bridge] theorem Mass0.toRat_idxProd (n : Count0) (f : Idx n → Mass0) :
    (Idx.prod n f).toRat = ∏ j : Fin n.toNat, (f (Idx.ofFin j)).toRat :=
  map_idxProd _ Mass0.toRat_mul Mass0.toRat_one n f

@[qpp_bridge] theorem Mass.toRat_idxProd (n : Count0) (f : Idx n → Mass) :
    (Idx.prod n f).toRat = ∏ j : Fin n.toNat, (f (Idx.ofFin j)).toRat :=
  map_idxProd _ Mass.toRat_mul Mass.toRat_one n f

@[qpp_bridge] theorem Count0.toNat_idxProd (n : Count0) (f : Idx n → Count0) :
    (Idx.prod n f).toNat = ∏ j : Fin n.toNat, (f (Idx.ofFin j)).toNat :=
  map_idxProd _ Count0.toNat_mul Count0.toNat_one n f

@[qpp_bridge] theorem Count.toNat_idxProd (n : Count0) (f : Idx n → Count) :
    (Idx.prod n f).toNat = ∏ j : Fin n.toNat, (f (Idx.ofFin j)).toNat :=
  map_idxProd _ Count.toNat_mul Count.toNat_one' n f

@[qpp_bridge] theorem Mass0.toRat_rangeSum (a b : Count0) (f : Count0 → Mass0) :
    (rangeSum a b f).toRat = ∑ v ∈ Icc a.toNat b.toNat, (f (Count0.ofNat v)).toRat :=
  map_rangeSum _ Mass0.toRat_add Mass0.toRat_zero a b f

@[qpp_bridge] theorem Count0.toNat_rangeSum (a b : Count0) (f : Count0 → Count0) :
    (rangeSum a b f).toNat = ∑ v ∈ Icc a.toNat b.toNat, (f (Count0.ofNat v)).toNat :=
  map_rangeSum _ Count0.toNat_add Count0.toNat_zero a b f

@[qpp_bridge] theorem Mass0.toRat_rangeProd (a b : Count0) (f : Count0 → Mass0) :
    (rangeProd a b f).toRat = ∏ v ∈ Icc a.toNat b.toNat, (f (Count0.ofNat v)).toRat :=
  map_rangeProd _ Mass0.toRat_mul Mass0.toRat_one a b f

@[qpp_bridge] theorem Mass.toRat_rangeProd (a b : Count0) (f : Count0 → Mass) :
    (rangeProd a b f).toRat = ∏ v ∈ Icc a.toNat b.toNat, (f (Count0.ofNat v)).toRat :=
  map_rangeProd _ Mass.toRat_mul Mass.toRat_one a b f

@[qpp_bridge] theorem Count0.toNat_rangeProd (a b : Count0) (f : Count0 → Count0) :
    (rangeProd a b f).toNat = ∏ v ∈ Icc a.toNat b.toNat, (f (Count0.ofNat v)).toNat :=
  map_rangeProd _ Count0.toNat_mul Count0.toNat_one a b f

@[qpp_bridge] theorem Count.toNat_rangeProd (a b : Count0) (f : Count0 → Count) :
    (rangeProd a b f).toNat = ∏ v ∈ Icc a.toNat b.toNat, (f (Count0.ofNat v)).toNat :=
  map_rangeProd _ Count.toNat_mul Count.toNat_one' a b f

/-! ## Quantifiers over counts and masses

A quantifier of the Mathlib reading over `ℕ`, over the positive integers, over the nonnegative or over the positive
rationals reads as a quantifier over `Count0`, `Count`, `Mass0` or `Mass`. A guarded quantifier is read first. -/

@[qpp_bridge] theorem Count0.forall_nat {P : ℕ → Prop} : (∀ n, P n) ↔ ∀ x : Count0, P x.toNat :=
  ⟨fun h _ => h _, fun h n => by rw [← Count0.toNat_ofNat n]; exact h _⟩

@[qpp_bridge] theorem Count0.exists_nat {P : ℕ → Prop} : (∃ n, P n) ↔ ∃ x : Count0, P x.toNat :=
  ⟨fun ⟨n, h⟩ => ⟨Count0.ofNat n, by rwa [Count0.toNat_ofNat]⟩, fun ⟨_, h⟩ => ⟨_, h⟩⟩

@[qpp_bridge high] theorem Count.forall_pos {P : ℕ → Prop} : (∀ n, 1 ≤ n → P n) ↔ ∀ c : Count, P c.toNat :=
  ⟨fun h c => h _ (Count.one_le_toNat c), fun h n hn => by rw [← Count.toNat_ofNat_of_pos hn]; exact h _⟩

@[qpp_bridge high] theorem Count.exists_pos {P : ℕ → Prop} : (∃ n, 1 ≤ n ∧ P n) ↔ ∃ c : Count, P c.toNat :=
  ⟨fun ⟨n, hn, h⟩ => ⟨Count.ofNat n, by rwa [Count.toNat_ofNat_of_pos hn]⟩,
    fun ⟨c, h⟩ => ⟨_, Count.one_le_toNat c, h⟩⟩

/-- A guarded quantifier over `Count0` whose guard is `1 ≤ x` (a count at least one, written `x in NN, 1 <= x`) reads
as a quantifier over `Count`, as the guarded quantifier over `ℕ` of the Mathlib reading does (`Count.forall_pos`), so
that the two readings meet. -/
@[qpp_bridge high] theorem Count0.forall_one_le {Q : Count0 → Prop} :
    (∀ x : Count0, 1 ≤ x.toNat → Q x) ↔ ∀ c : Count, Q (Count0.of c) :=
  ⟨fun h c => h _ (Count.one_le_toNat c), fun h x hx => by
    have e : Count0.of (Count.ofNat x.toNat) = x :=
      Count0.toNat_injective (by rw [Count0.toNat_of, Count.toNat_ofNat_of_pos hx])
    exact e ▸ h _⟩

@[qpp_bridge high] theorem Count0.exists_one_le {Q : Count0 → Prop} :
    (∃ x : Count0, 1 ≤ x.toNat ∧ Q x) ↔ ∃ c : Count, Q (Count0.of c) :=
  ⟨fun ⟨x, hx, h⟩ => ⟨Count.ofNat x.toNat, by
      have e : Count0.of (Count.ofNat x.toNat) = x :=
        Count0.toNat_injective (by rw [Count0.toNat_of, Count.toNat_ofNat_of_pos hx])
      rw [e]; exact h⟩,
    fun ⟨c, h⟩ => ⟨Count0.of c, Count.one_le_toNat c, h⟩⟩

@[qpp_bridge high] theorem Mass.forall_pos {P : ℚ → Prop} : (∀ q, 0 < q → P q) ↔ ∀ x : Mass, P x.toRat :=
  ⟨fun h x => h _ (Mass.toRat_pos x), fun h q hq => by rw [← Mass.toRat_ofRat hq]; exact h _⟩

@[qpp_bridge high] theorem Mass.exists_pos {P : ℚ → Prop} : (∃ q, 0 < q ∧ P q) ↔ ∃ x : Mass, P x.toRat :=
  ⟨fun ⟨q, hq, h⟩ => ⟨Mass.ofRat q, by rwa [Mass.toRat_ofRat hq]⟩, fun ⟨x, h⟩ => ⟨_, Mass.toRat_pos x, h⟩⟩

@[qpp_bridge high] theorem Mass0.forall_nonneg {P : ℚ → Prop} : (∀ q, 0 ≤ q → P q) ↔ ∀ x : Mass0, P x.toRat :=
  ⟨fun h x => h _ (Mass0.toRat_nonneg x), fun h q hq => by rw [← Mass0.toRat_ofRat hq]; exact h _⟩

@[qpp_bridge high] theorem Mass0.exists_nonneg {P : ℚ → Prop} : (∃ q, 0 ≤ q ∧ P q) ↔ ∃ x : Mass0, P x.toRat :=
  ⟨fun ⟨q, hq, h⟩ => ⟨Mass0.ofRat q, by rwa [Mass0.toRat_ofRat hq]⟩, fun ⟨x, h⟩ => ⟨_, Mass0.toRat_nonneg x, h⟩⟩

/-! ## Quantifiers over tuples: a tuple of counts or absent is a tuple of `ℕ`, a tuple of masses or absent a tuple of
`ℚ≥0` -/

theorem Idx.unmap_map {n : Count0} {X Y : Type} (φ : X → Y) (ψ : Y → X) (h : ∀ x, ψ (φ x) = x) (u : Idx n → X) :
    Idx.unmap ψ (Idx.map φ u) = u := by
  funext i; rw [Idx.unmap_apply, Idx.map_apply, Idx.ofFin_toFin, h]

theorem Idx.map_unmap {n : Count0} {X Y : Type} (φ : X → Y) (ψ : Y → X) (h : ∀ y, φ (ψ y) = y)
    (v : Fin n.toNat → Y) : Idx.map φ (Idx.unmap ψ v) = v := by
  funext j; rw [Idx.map_apply, Idx.unmap_apply, Idx.toFin_ofFin, h]

/-- A quantifier over the tuples of `X`, read through a reading `φ` of `X` with a left inverse `ψ`. -/
theorem Idx.forall_read {n : Count0} {X Y : Type} (φ : X → Y) (ψ : Y → X) (h : ∀ x, ψ (φ x) = x)
    {P : (Idx n → X) → Prop} : (∀ x, P x) ↔ ∀ y : Fin n.toNat → Y, P (Idx.unmap ψ y) :=
  ⟨fun hP _ => hP _, fun hP x => by rw [← Idx.unmap_map φ ψ h x]; exact hP _⟩

theorem Idx.exists_read {n : Count0} {X Y : Type} (φ : X → Y) (ψ : Y → X) (h : ∀ x, ψ (φ x) = x)
    {P : (Idx n → X) → Prop} : (∃ x, P x) ↔ ∃ y : Fin n.toNat → Y, P (Idx.unmap ψ y) :=
  ⟨fun ⟨x, hx⟩ => ⟨Idx.map φ x, by rwa [Idx.unmap_map φ ψ h x]⟩, fun ⟨_, hy⟩ => ⟨_, hy⟩⟩

theorem Idx.eq_unmap {n : Count0} {X Y : Type} (φ : X → Y) (ψ : Y → X) (h : ∀ x, ψ (φ x) = x)
    (h' : ∀ y, φ (ψ y) = y) (x : Idx n → X) (y : Fin n.toNat → Y) : x = Idx.unmap ψ y ↔ Idx.map φ x = y :=
  ⟨fun e => e ▸ Idx.map_unmap φ ψ h' y, fun e => e ▸ (Idx.unmap_map φ ψ h x).symm⟩

theorem Mass0.toNNRat_ofNNRat (q : ℚ≥0) : Mass0.toNNRat (Mass0.ofNNRat q) = q := Mass0.equivNNRat.right_inv q

/-! The tuples of counts or absent, and of masses or absent. -/

@[qpp_bridge] theorem Idx.forall_count0 {n : Count0} {P : (Idx n → Count0) → Prop} :
    (∀ x, P x) ↔ ∀ y : Fin n.toNat → ℕ, P (Idx.unmap Count0.ofNat y) :=
  Idx.forall_read Count0.toNat Count0.ofNat Count0.ofNat_toNat

@[qpp_bridge] theorem Idx.exists_count0 {n : Count0} {P : (Idx n → Count0) → Prop} :
    (∃ x, P x) ↔ ∃ y : Fin n.toNat → ℕ, P (Idx.unmap Count0.ofNat y) :=
  Idx.exists_read Count0.toNat Count0.ofNat Count0.ofNat_toNat

@[qpp_bridge] theorem Idx.forall_mass0 {n : Count0} {P : (Idx n → Mass0) → Prop} :
    (∀ x, P x) ↔ ∀ y : Fin n.toNat → ℚ≥0, P (Idx.unmap Mass0.ofNNRat y) :=
  Idx.forall_read Mass0.toNNRat Mass0.ofNNRat Mass0.ofNNRat_toNNRat

@[qpp_bridge] theorem Idx.exists_mass0 {n : Count0} {P : (Idx n → Mass0) → Prop} :
    (∃ x, P x) ↔ ∃ y : Fin n.toNat → ℚ≥0, P (Idx.unmap Mass0.ofNNRat y) :=
  Idx.exists_read Mass0.toNNRat Mass0.ofNNRat Mass0.ofNNRat_toNNRat

/-- A quantifier over the functions on the tuples of counts or absent, valued in the masses or absent (a function on
the lattice points of a box), read through the reading of its points and of its values. -/
@[qpp_bridge] theorem Idx.forall_fun_count0 {n : Count0} {P : ((Idx n → Count0) → Mass0) → Prop} :
    (∀ G, P G) ↔ ∀ H : (Fin n.toNat → ℕ) → ℚ≥0, P (fun u => Mass0.ofNNRat (H (Idx.map Count0.toNat u))) := by
  refine ⟨fun h _ => h _, fun h G => ?_⟩
  have e : (fun u => Mass0.ofNNRat ((fun v => Mass0.toNNRat (G (Idx.unmap Count0.ofNat v)))
      (Idx.map Count0.toNat u))) = G := by
    funext u; simp only [Idx.unmap_map Count0.toNat Count0.ofNat Count0.ofNat_toNat, Mass0.ofNNRat_toNNRat]
  rw [← e]; exact h (fun v => Mass0.toNNRat (G (Idx.unmap Count0.ofNat v)))

@[qpp_bridge] theorem Idx.exists_fun_count0 {n : Count0} {P : ((Idx n → Count0) → Mass0) → Prop} :
    (∃ G, P G) ↔ ∃ H : (Fin n.toNat → ℕ) → ℚ≥0, P (fun u => Mass0.ofNNRat (H (Idx.map Count0.toNat u))) := by
  refine ⟨fun ⟨G, hG⟩ => ⟨fun v => Mass0.toNNRat (G (Idx.unmap Count0.ofNat v)), ?_⟩, fun ⟨_, h⟩ => ⟨_, h⟩⟩
  have e : (fun u => Mass0.ofNNRat ((fun v => Mass0.toNNRat (G (Idx.unmap Count0.ofNat v)))
      (Idx.map Count0.toNat u))) = G := by
    funext u; simp only [Idx.unmap_map Count0.toNat Count0.ofNat Count0.ofNat_toNat, Mass0.ofNNRat_toNNRat]
  rw [e]; exact hG

@[qpp_bridge] theorem Idx.unmap_map_count0 {n : Count0} (x : Idx n → Count0) :
    Idx.unmap Count0.ofNat (Idx.map Count0.toNat x) = x :=
  Idx.unmap_map Count0.toNat Count0.ofNat Count0.ofNat_toNat x

@[qpp_bridge] theorem Idx.unmap_map_mass0 {n : Count0} (x : Idx n → Mass0) :
    Idx.unmap Mass0.ofNNRat (Idx.map Mass0.toNNRat x) = x :=
  Idx.unmap_map Mass0.toNNRat Mass0.ofNNRat Mass0.ofNNRat_toNNRat x

@[qpp_bridge] theorem Idx.eq_unmap_count0 {n : Count0} (x : Idx n → Count0) (y : Fin n.toNat → ℕ) :
    x = Idx.unmap Count0.ofNat y ↔ Idx.map Count0.toNat x = y :=
  Idx.eq_unmap _ _ Count0.ofNat_toNat Count0.toNat_ofNat x y

@[qpp_bridge] theorem Idx.eq_unmap_mass0 {n : Count0} (x : Idx n → Mass0) (y : Fin n.toNat → ℚ≥0) :
    x = Idx.unmap Mass0.ofNNRat y ↔ Idx.map Mass0.toNNRat x = y :=
  Idx.eq_unmap _ _ Mass0.ofNNRat_toNNRat Mass0.toNNRat_ofNNRat x y

/-! The tuples of tuples, `(X^n)^k`: a tuple of `k` tuples of `n` entries. -/

@[qpp_bridge] theorem Idx.forall_count0₂ {k n : Count0} {P : (Idx k → Idx n → Count0) → Prop} :
    (∀ x, P x) ↔ ∀ y : Fin k.toNat → Fin n.toNat → ℕ, P (Idx.unmap (Idx.unmap Count0.ofNat) y) :=
  Idx.forall_read (Idx.map Count0.toNat) (Idx.unmap Count0.ofNat) Idx.unmap_map_count0

@[qpp_bridge] theorem Idx.exists_count0₂ {k n : Count0} {P : (Idx k → Idx n → Count0) → Prop} :
    (∃ x, P x) ↔ ∃ y : Fin k.toNat → Fin n.toNat → ℕ, P (Idx.unmap (Idx.unmap Count0.ofNat) y) :=
  Idx.exists_read (Idx.map Count0.toNat) (Idx.unmap Count0.ofNat) Idx.unmap_map_count0

@[qpp_bridge] theorem Idx.forall_mass0₂ {k n : Count0} {P : (Idx k → Idx n → Mass0) → Prop} :
    (∀ x, P x) ↔ ∀ y : Fin k.toNat → Fin n.toNat → ℚ≥0, P (Idx.unmap (Idx.unmap Mass0.ofNNRat) y) :=
  Idx.forall_read (Idx.map Mass0.toNNRat) (Idx.unmap Mass0.ofNNRat) Idx.unmap_map_mass0

@[qpp_bridge] theorem Idx.exists_mass0₂ {k n : Count0} {P : (Idx k → Idx n → Mass0) → Prop} :
    (∃ x, P x) ↔ ∃ y : Fin k.toNat → Fin n.toNat → ℚ≥0, P (Idx.unmap (Idx.unmap Mass0.ofNNRat) y) :=
  Idx.exists_read (Idx.map Mass0.toNNRat) (Idx.unmap Mass0.ofNNRat) Idx.unmap_map_mass0

@[qpp_bridge] theorem Idx.unmap_map_count0₂ {k n : Count0} (x : Idx k → Idx n → Count0) :
    Idx.unmap (Idx.unmap Count0.ofNat) (Idx.map (Idx.map Count0.toNat) x) = x :=
  Idx.unmap_map _ _ Idx.unmap_map_count0 x

@[qpp_bridge] theorem Idx.unmap_map_mass0₂ {k n : Count0} (x : Idx k → Idx n → Mass0) :
    Idx.unmap (Idx.unmap Mass0.ofNNRat) (Idx.map (Idx.map Mass0.toNNRat) x) = x :=
  Idx.unmap_map _ _ Idx.unmap_map_mass0 x

@[qpp_bridge] theorem Idx.map_unmap_count0₂ {k n : Count0} (y : Fin k.toNat → Fin n.toNat → ℕ) :
    Idx.map (Idx.map Count0.toNat) (Idx.unmap (Idx.unmap Count0.ofNat) y) = y :=
  Idx.map_unmap _ _ (Idx.map_unmap _ _ Count0.toNat_ofNat) y

@[qpp_bridge] theorem Idx.map_unmap_mass0₂ {k n : Count0} (y : Fin k.toNat → Fin n.toNat → ℚ≥0) :
    Idx.map (Idx.map Mass0.toNNRat) (Idx.unmap (Idx.unmap Mass0.ofNNRat) y) = y :=
  Idx.map_unmap _ _ (Idx.map_unmap _ _ Mass0.toNNRat_ofNNRat) y

@[qpp_bridge] theorem Idx.map_unmap_count0 {n : Count0} (y : Fin n.toNat → ℕ) :
    Idx.map Count0.toNat (Idx.unmap Count0.ofNat y) = y :=
  Idx.map_unmap _ _ Count0.toNat_ofNat y

@[qpp_bridge] theorem Idx.map_unmap_mass0 {n : Count0} (y : Fin n.toNat → ℚ≥0) :
    Idx.map Mass0.toNNRat (Idx.unmap Mass0.ofNNRat y) = y :=
  Idx.map_unmap _ _ Mass0.toNNRat_ofNNRat y

/-- The deficit of two counts, read in the rationals. -/
@[qpp_bridge] theorem cast_deficit (a b : ℕ) : (((max (a - b) 0 : ℕ)) : ℚ) = max ((a : ℚ) - b) 0 := by
  rcases le_total b a with h | h
  · rw [Nat.cast_max, Nat.cast_sub h, Nat.cast_zero]
  · rw [Nat.sub_eq_zero_of_le h, max_self, Nat.cast_zero, eq_comm, max_eq_right]; linarith [(Nat.cast_le (α := ℚ)).2 h]

theorem Count0.forall_iff {P : Count0 → Prop} : (∀ x, P x) ↔ ∀ v : ℕ, P (Count0.ofNat v) :=
  ⟨fun h v => h _, fun h x => by rw [← Count0.ofNat_toNat x]; exact h _⟩

theorem Count0.exists_iff {P : Count0 → Prop} : (∃ x, P x) ↔ ∃ v : ℕ, P (Count0.ofNat v) :=
  ⟨fun ⟨x, h⟩ => ⟨x.toNat, by rwa [Count0.ofNat_toNat]⟩, fun ⟨v, h⟩ => ⟨_, h⟩⟩

/-! ## Families

A family `a_(1..k) in X` over the kernel is `a : Count0 → X`, read as the function of the naturals `i ↦ a (ofNat i)`,
its members read. A quantifier of the reading over the families of `ℕ` or `ℚ`, with the bound of `X` at every
member, reads as one over the families of the kernel; the guarded forms take priority. The bound is stated as the
simp set leaves it once its own quantifier over `ℕ` is read (`∀ x : Count0, 0 ≤ a x.toNat`), since simp reads the
inner quantifiers first. -/

section Families

variable {P : (ℕ → ℕ) → Prop} {Q : (ℕ → ℚ) → Prop}

@[qpp_bridge] theorem Count0.forall_fam :
    (∀ a : ℕ → ℕ, P a) ↔ ∀ a : Count0 → Count0, P (fun i => (a (Count0.ofNat i)).toNat) := by
  refine ⟨fun h a => h _, fun h a => ?_⟩
  have e : (fun i => (Count0.ofNat (a (Count0.ofNat i).toNat)).toNat) = a :=
    funext fun i => by rw [Count0.toNat_ofNat, Count0.toNat_ofNat]
  simpa only [e] using h (fun c => Count0.ofNat (a c.toNat))

@[qpp_bridge] theorem Count0.exists_fam :
    (∃ a : ℕ → ℕ, P a) ↔ ∃ a : Count0 → Count0, P (fun i => (a (Count0.ofNat i)).toNat) := by
  refine ⟨fun ⟨a, h⟩ => ⟨fun c => Count0.ofNat (a c.toNat), ?_⟩, fun ⟨_, h⟩ => ⟨_, h⟩⟩
  have e : (fun i => (Count0.ofNat (a (Count0.ofNat i).toNat)).toNat) = a :=
    funext fun i => by rw [Count0.toNat_ofNat, Count0.toNat_ofNat]
  simpa only [e] using h

/-- The bound `1 ≤ a i` at every member, read over the counts or absent. -/
theorem Count.fam_bound {a : ℕ → ℕ} (ha : ∀ x : Count0, 1 ≤ a x.toNat) (i : ℕ) : 0 < a i := by
  have := ha (Count0.ofNat i); rwa [Count0.toNat_ofNat] at this

/-- The bound `0 ≤ a i` at every member, read over the counts or absent. -/
theorem Mass0.fam_bound {a : ℕ → ℚ} (ha : ∀ x : Count0, 0 ≤ a x.toNat) (i : ℕ) : 0 ≤ a i := by
  have := ha (Count0.ofNat i); rwa [Count0.toNat_ofNat] at this

/-- The bound `0 < a i` at every member, read over the counts or absent. -/
theorem Mass.fam_bound {a : ℕ → ℚ} (ha : ∀ x : Count0, 0 < a x.toNat) (i : ℕ) : 0 < a i := by
  have := ha (Count0.ofNat i); rwa [Count0.toNat_ofNat] at this

@[qpp_bridge high] theorem Count.forall_fam :
    (∀ a : ℕ → ℕ, (∀ x : Count0, 1 ≤ a x.toNat) → P a) ↔
      ∀ a : Count0 → Count, P (fun i => (a (Count0.ofNat i)).toNat) := by
  refine ⟨fun h a => h _ (fun _ => Count.one_le_toNat _), fun h a ha => ?_⟩
  have e : (fun i => (Count.ofNat (a (Count0.ofNat i).toNat)).toNat) = a :=
    funext fun i => by rw [Count0.toNat_ofNat, Count.toNat_ofNat_of_pos (Count.fam_bound ha i)]
  simpa only [e] using h (fun c => Count.ofNat (a c.toNat))

@[qpp_bridge high] theorem Count.exists_fam :
    (∃ a : ℕ → ℕ, (∀ x : Count0, 1 ≤ a x.toNat) ∧ P a) ↔
      ∃ a : Count0 → Count, P (fun i => (a (Count0.ofNat i)).toNat) := by
  refine ⟨fun ⟨a, ha, h⟩ => ⟨fun c => Count.ofNat (a c.toNat), ?_⟩,
    fun ⟨_, h⟩ => ⟨_, fun _ => Count.one_le_toNat _, h⟩⟩
  have e : (fun i => (Count.ofNat (a (Count0.ofNat i).toNat)).toNat) = a :=
    funext fun i => by rw [Count0.toNat_ofNat, Count.toNat_ofNat_of_pos (Count.fam_bound ha i)]
  simpa only [e] using h

@[qpp_bridge high] theorem Mass0.forall_fam :
    (∀ a : ℕ → ℚ, (∀ x : Count0, 0 ≤ a x.toNat) → Q a) ↔
      ∀ a : Count0 → Mass0, Q (fun i => (a (Count0.ofNat i)).toRat) := by
  refine ⟨fun h a => h _ (fun _ => Mass0.toRat_nonneg _), fun h a ha => ?_⟩
  have e : (fun i => (Mass0.ofRat (a (Count0.ofNat i).toNat)).toRat) = a :=
    funext fun i => by rw [Count0.toNat_ofNat, Mass0.toRat_ofRat (Mass0.fam_bound ha i)]
  simpa only [e] using h (fun c => Mass0.ofRat (a c.toNat))

@[qpp_bridge high] theorem Mass0.exists_fam :
    (∃ a : ℕ → ℚ, (∀ x : Count0, 0 ≤ a x.toNat) ∧ Q a) ↔
      ∃ a : Count0 → Mass0, Q (fun i => (a (Count0.ofNat i)).toRat) := by
  refine ⟨fun ⟨a, ha, h⟩ => ⟨fun c => Mass0.ofRat (a c.toNat), ?_⟩,
    fun ⟨_, h⟩ => ⟨_, fun _ => Mass0.toRat_nonneg _, h⟩⟩
  have e : (fun i => (Mass0.ofRat (a (Count0.ofNat i).toNat)).toRat) = a :=
    funext fun i => by rw [Count0.toNat_ofNat, Mass0.toRat_ofRat (Mass0.fam_bound ha i)]
  simpa only [e] using h

@[qpp_bridge high] theorem Mass.forall_fam :
    (∀ a : ℕ → ℚ, (∀ x : Count0, 0 < a x.toNat) → Q a) ↔
      ∀ a : Count0 → Mass, Q (fun i => (a (Count0.ofNat i)).toRat) := by
  refine ⟨fun h a => h _ (fun _ => Mass.toRat_pos _), fun h a ha => ?_⟩
  have e : (fun i => (Mass.ofRat (a (Count0.ofNat i).toNat)).toRat) = a :=
    funext fun i => by rw [Count0.toNat_ofNat, Mass.toRat_ofRat (Mass.fam_bound ha i)]
  simpa only [e] using h (fun c => Mass.ofRat (a c.toNat))

@[qpp_bridge high] theorem Mass.exists_fam :
    (∃ a : ℕ → ℚ, (∀ x : Count0, 0 < a x.toNat) ∧ Q a) ↔
      ∃ a : Count0 → Mass, Q (fun i => (a (Count0.ofNat i)).toRat) := by
  refine ⟨fun ⟨a, ha, h⟩ => ⟨fun c => Mass.ofRat (a c.toNat), ?_⟩,
    fun ⟨_, h⟩ => ⟨_, fun _ => Mass.toRat_pos _, h⟩⟩
  have e : (fun i => (Mass.ofRat (a (Count0.ofNat i).toNat)).toRat) = a :=
    funext fun i => by rw [Count0.toNat_ofNat, Mass.toRat_ofRat (Mass.fam_bound ha i)]
  simpa only [e] using h

end Families

end Qpp
