module

public import QppBridge.Pair
public import QppBridge.Box
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Order.Bounds.Defs

/-!
# The bridge of the program atom

`prog(S : c) = P` of the kernel (`IsProg`) is read as `Pair.IsProg` of Mathlib: the least cost is `IsLeast` of the
image of the costs, and the dimension of the face of the least cost is the `finrank` of its `vectorSpan`. A point of
the kernel is read by its coordinates (`Idx.map Mass0.toRat`), and the points read are the points of the feasible set
of Mathlib, whose coordinates are at least `0`.

The dimension of the kernel is the largest number of points of the face, after a first, whose differences from the
first are linearly independent, with balances as coefficients; read in `ℚ`, it is the `finrank` of the `vectorSpan` of
the face (`QppMathlib.exists_indep_iff`, from Mathlib's spanning linearly independent subsets).
-/

@[expose] public section

namespace QppMathlib

open Module

/-- `prog(S : c) = p`: `p` is `⊤` and no point of `S` is feasible, or `p` stores the least value `L` of the cost `c`
over `S` and the dimension of the set of points of `S` of cost `L`. -/
def Pair.IsProg {k : ℕ} (S : Set (Fin k → ℚ)) (c : (Fin k → ℚ) → ℚ) (p : Pair) : Prop :=
  (p = ⊤ ∧ S = ∅) ∨
    ∃ L : NNRat, IsLeast (c '' S) (L : ℚ) ∧
      p = Pair.mk L (Module.finrank ℚ (vectorSpan ℚ {x | x ∈ S ∧ c x = L}))

section Dim

variable {V : Type} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

/-- A nonempty set has `d + 1` points whose differences from the first are linearly independent exactly when `d` is at
most the dimension of its `vectorSpan`. -/
theorem exists_indep_iff (F : Set V) (hF : F.Nonempty) (d : ℕ) :
    (∃ p : ℕ → V, (∀ j ≤ d, p j ∈ F) ∧ LinearIndependent ℚ (fun j : Fin d => p (j + 1) - p 0)) ↔
      d ≤ finrank ℚ (vectorSpan ℚ F) := by
  constructor
  · rintro ⟨p, hp, hli⟩
    have h1 := finrank_span_eq_card hli
    rw [Fintype.card_fin] at h1
    rw [← h1]
    apply Submodule.finrank_mono
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have := vsub_mem_vectorSpan ℚ (hp (j + 1) (by omega)) (hp 0 (Nat.zero_le _))
    rw [SetLike.mem_coe]; simpa only [vsub_eq_sub] using this
  · intro hd
    obtain ⟨x0, hx0⟩ := hF
    rw [vectorSpan_eq_span_vsub_set_right ℚ hx0] at hd
    obtain ⟨b, hbW, hspan, hli⟩ := exists_linearIndependent ℚ ((fun x => x -ᵥ x0) '' F)
    have := hli.setFinite.fintype
    have hcard := finrank_span_eq_card hli
    rw [Subtype.range_coe, hspan] at hcard
    rw [hcard] at hd
    let e : Fin d ↪ b := (Fin.castLEEmb hd).trans (Fintype.equivFin b).symm.toEmbedding
    have hv : ∀ j : Fin d, ∃ q ∈ F, q - x0 = (e j : V) := fun j => by
      obtain ⟨q, hq, h⟩ := hbW (e j).2
      exact ⟨q, hq, by simpa only [vsub_eq_sub] using h⟩
    choose q hqF hq using hv
    let p : ℕ → V := fun j => match j with
      | 0 => x0
      | j + 1 => if h : j < d then q ⟨j, h⟩ else x0
    refine ⟨p, fun j _ => ?_, ?_⟩
    · cases j with
      | zero => exact hx0
      | succ j =>
        show (if h : j < d then q ⟨j, h⟩ else x0) ∈ F
        split_ifs
        · exact hqF _
        · exact hx0
    · have : (fun j : Fin d => p (j + 1) - p 0) = (Subtype.val ∘ e) := by
        funext j
        show (if h : j.1 < d then q ⟨j.1, h⟩ else x0) - x0 = _
        rw [dite_eq_left j.2]; exact hq j
      rw [this]
      exact hli.comp e e.injective

end Dim

end QppMathlib

namespace Qpp

open Module

variable {k : Count0}

/-- The points `p_0, p_1, ...` of the kernel read in Mathlib. -/
noncomputable def readPts (p : Count0 → Idx k → Mass0) (j : ℕ) : Fin k.toNat → ℚ :=
  Idx.map Mass0.toRat (p (Count0.ofNat j))

theorem readPts_apply (p : Count0 → Idx k → Mass0) (j : ℕ) (t : Fin k.toNat) :
    readPts p j t = (p (Count0.ofNat j) (Idx.ofFin t)).toRat := rfl

theorem toRat_faceComb (d : Count) (p : Count0 → Idx k → Mass0) (y : Count → Bal Mass) (i : Idx k) :
    (faceComb d p y i).toRat = ∑ j : Fin d.toNat,
      (y (Count.ofNatSucc j.1)).toRat * (readPts p (j + 1) (Idx.toFin i) - readPts p 0 (Idx.toFin i)) := by
  unfold faceComb
  rw [map_sumTo Bal.toRat Bal.toRat_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Bal.toRat_mul, Bal.toRat_add, Bal.toRat_swap, Mass0.toRat_toBal, Mass0.toRat_toBal, readPts_apply,
    readPts_apply, Idx.ofFin_toFin, sub_eq_add_neg]
  rfl

/-- The differences of the points of the kernel are independent, with balances as coefficients, exactly when their
readings are linearly independent. -/
theorem linIndep_iff (d : Count) (p : Count0 → Idx k → Mass0) :
    (∀ y : Count → Bal Mass, (∀ i, Bal.Tie (faceComb d p y i) Bal.level) →
        ∀ j : Count, Count0.of j ≤ Count0.of d → Bal.Tie (y j) Bal.level) ↔
      LinearIndependent ℚ (fun j : Fin d.toNat => readPts p (j + 1) - readPts p 0) := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h g hg j
    let y : Count → Bal Mass := fun c => Bal.ofRat (if h : c.toNat - 1 < d.toNat then g ⟨c.toNat - 1, h⟩ else 0)
    have hy : ∀ j : Fin d.toNat, (y (Count.ofNatSucc j.1)).toRat = g j := fun j => by
      show (Bal.ofRat _).toRat = _
      rw [Bal.toRat_ofRat]
      have e : (Count.ofNatSucc j.1).toNat - 1 = j.1 := by rw [Count.toNat_ofNatSucc]; omega
      rw [dite_eq_left (by rw [e]; exact j.2)]
      congr 1; exact Fin.ext e
    have hk := h y (fun i => by
      rw [Bal.tie_iff, toRat_faceComb, Bal.toRat_level]
      have := congrFun hg (Idx.toFin i)
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => by rw [hy j])
      (Count.ofNatSucc j.1) (by rw [Count0.toNat_le, Count0.toNat_of, Count.toNat_ofNatSucc]; exact j.2)
    rw [Bal.tie_iff, Bal.toRat_level, hy j] at hk
    exact hk
  · intro h y hy j hj
    have hg := h (fun j => (y (Count.ofNatSucc j.1)).toRat) (by
      funext t
      have := hy (Idx.ofFin t)
      rw [Bal.tie_iff, toRat_faceComb, Bal.toRat_level, Idx.toFin_ofFin] at this
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
      exact this)
    have hj' : j.toNat - 1 < d.toNat := by
      rw [Count0.toNat_le, Count0.toNat_of, Count0.toNat_of] at hj; have := Count.toNat_pos j
      show j.toNat - 1 < d.toNat; omega
    have := hg ⟨j.toNat - 1, hj'⟩
    have e : Count.ofNatSucc (j.toNat - 1) = j :=
      Count.toNat_inj (by rw [Count.toNat_ofNatSucc]; have := Count.toNat_pos j; omega)
    simp only [e] at this
    rw [Bal.tie_iff, Bal.toRat_level]; exact this

section Face

variable (F : (Idx k → Mass0) → Prop) (F' : Set (Fin k.toNat → ℚ))

/-- Affinely independent points of the kernel read as points of Mathlib with linearly independent differences. -/
theorem affIndep_iff (hF : ∀ x, F x ↔ Idx.map Mass0.toRat x ∈ F') (d : Count0) (p : Count0 → Idx k → Mass0) :
    AffIndep F d p ↔ (∀ j ≤ d.toNat, readPts p j ∈ F') ∧
      LinearIndependent ℚ (fun j : Fin d.toNat => readPts p (j + 1) - readPts p 0) := by
  have h1 : (∀ j : Count0, j ≤ d → F (p j)) ↔ ∀ j ≤ d.toNat, readPts p j ∈ F' := by
    rw [Count0.forall_iff]
    refine forall_congr' fun v => ?_
    rw [Count0.toNat_le, Count0.toNat_ofNat, hF]; rfl
  unfold AffIndep
  rw [h1]
  refine and_congr Iff.rfl ?_
  induction d using Count0.cases' with
  | h0 =>
    have : IsEmpty (Fin (Count0.toNat 0)) := ⟨fun j => Nat.not_lt_zero _ j.2⟩
    exact iff_of_true trivial linearIndependent_empty_type
  | hs d => exact linIndep_iff d p

theorem readPts_unmap (P : ℕ → Fin k.toNat → ℚ) (j : ℕ) (hj : ∀ t, 0 ≤ P j t) :
    readPts (fun j i => Mass0.ofRat (P j.toNat (Idx.toFin i))) j = P j := by
  funext t
  rw [readPts_apply, Idx.toFin_ofFin, Count0.toNat_ofNat, Mass0.toRat_ofRat (hj t)]

variable (hF : ∀ x, F x ↔ Idx.map Mass0.toRat x ∈ F') (hF0 : ∀ y ∈ F', ∀ i, 0 ≤ y i)
include hF hF0

theorem exists_affIndep_iff (hne : F'.Nonempty) (d : Count0) :
    (∃ p, AffIndep F d p) ↔ d.toNat ≤ finrank ℚ (vectorSpan ℚ F') := by
  rw [← QppMathlib.exists_indep_iff F' hne]
  constructor
  · rintro ⟨p, h⟩
    exact ⟨readPts p, (affIndep_iff F F' hF d p).1 h⟩
  · rintro ⟨P, hP, hli⟩
    refine ⟨fun j i => Mass0.ofRat (P j.toNat (Idx.toFin i)), (affIndep_iff F F' hF d _).2 ⟨fun j hj => ?_, ?_⟩⟩
    · rw [readPts_unmap P j (hF0 _ (hP j hj))]; exact hP j hj
    · have : (fun j : Fin d.toNat => readPts (fun j i => Mass0.ofRat (P j.toNat (Idx.toFin i))) (j + 1) -
          readPts (fun j i => Mass0.ofRat (P j.toNat (Idx.toFin i))) 0) = fun j : Fin d.toNat => P (j + 1) - P 0 := by
        funext j
        rw [readPts_unmap P (j + 1) (hF0 _ (hP _ j.2)), readPts_unmap P 0 (hF0 _ (hP 0 (Nat.zero_le _)))]
      rw [this]; exact hli

/-- The dimension of a face of the kernel is the `finrank` of the `vectorSpan` of its reading. -/
theorem faceDim_iff (hne : F'.Nonempty) (d : Count0) :
    FaceDim F d ↔ d.toNat = finrank ℚ (vectorSpan ℚ F') := by
  unfold FaceDim
  rw [exists_affIndep_iff F F' hF hF0 hne]
  have h2 : (∀ e : Count0, d < e → ∀ p, ¬ AffIndep F e p) ↔ finrank ℚ (vectorSpan ℚ F') ≤ d.toNat := by
    constructor
    · intro h
      by_contra hlt
      have := h (Count0.ofNat (d.toNat + 1)) (by rw [Count0.toNat_lt, Count0.toNat_ofNat]; omega)
      rw [← not_exists, exists_affIndep_iff F F' hF hF0 hne, Count0.toNat_ofNat] at this
      omega
    · intro h e he p hp
      have := (exists_affIndep_iff F F' hF hF0 hne e).1 ⟨p, hp⟩
      rw [Count0.toNat_lt] at he
      omega
  rw [h2]; omega

end Face

theorem map_unmap (y : Fin k.toNat → ℚ) (hy : ∀ i, 0 ≤ y i) :
    Idx.map Mass0.toRat (Idx.unmap Mass0.ofRat y) = y := by
  funext t
  rw [Idx.map_apply, Idx.unmap_apply, Idx.toFin_ofFin, Mass0.toRat_ofRat (hy t)]

/-- `prog(S : c) = P` over the kernel is `Pair.IsProg` of the readings, for a feasible set of Mathlib whose points are
the readings of the feasible points of the kernel. -/
theorem isProg_iff (S : (Idx k → Mass0) → Prop) (c : (Idx k → Mass0) → Mass0)
    (S' : Set (Fin k.toNat → ℚ)) (c' : (Fin k.toNat → ℚ) → ℚ)
    (hS : ∀ x, S x ↔ Idx.map Mass0.toRat x ∈ S') (hS0 : ∀ y ∈ S', ∀ i, 0 ≤ y i)
    (hc : ∀ x, (c x).toRat = c' (Idx.map Mass0.toRat x)) (P : PairLM) :
    IsProg S c P ↔ QppMathlib.Pair.IsProg S' c' P.toMath := by
  have back : ∀ y ∈ S', S (Idx.unmap Mass0.ofRat y) ∧ Idx.map Mass0.toRat (Idx.unmap Mass0.ofRat y) = y :=
    fun y hy => by
      have e := map_unmap y (hS0 y hy)
      exact ⟨(hS _).2 (by rw [e]; exact hy), e⟩
  cases P with
  | top =>
    show (∀ x, ¬ S x) ↔ _
    unfold QppMathlib.Pair.IsProg
    rw [PairLM.toMath_top]
    have hno : ¬ ∃ L : NNRat, _root_.IsLeast (c' '' S') (L : ℚ) ∧ (⊤ : QppMathlib.Pair) = QppMathlib.Pair.mk L
        (finrank ℚ (vectorSpan ℚ {x | x ∈ S' ∧ c' x = L})) := fun ⟨_, _, h⟩ => WithTop.top_ne_coe h
    rw [or_iff_left hno, eq_self_iff_true, true_and, Set.eq_empty_iff_forall_notMem]
    constructor
    · intro h y hy; exact h _ (back y hy).1
    · intro h x hx; exact h _ ((hS x).1 hx)
  | mk L m =>
    show (ProgLeast S c L ∧ ∃ d : Count0, FaceDim (fun x => S x ∧ c x = L) d ∧ Count0.of m = d + 1) ↔ _
    unfold QppMathlib.Pair.IsProg
    rw [PairLM.toMath_mk]
    have hno : ¬ (QppMathlib.Pair.mk L.toNNRat (m.toNat - 1) = ⊤ ∧ S' = ∅) := fun ⟨h, _⟩ => WithTop.coe_ne_top h
    rw [or_iff_right hno]
    have hL : ProgLeast S c L ↔ _root_.IsLeast (c' '' S') L.toRat := by
      constructor
      · rintro ⟨⟨x, hx, hcx⟩, hlow⟩
        refine ⟨⟨_, (hS x).1 hx, by rw [← hc, hcx]⟩, ?_⟩
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨hSy, e⟩ := back y hy
        have := Mass0.toRat_le.1 (hlow _ hSy)
        rwa [hc, e] at this
      · rintro ⟨⟨y, hy, hcy⟩, hlow⟩
        obtain ⟨hSy, e⟩ := back y hy
        refine ⟨⟨_, hSy, Mass0.toRat_eq.2 (by rw [hc, e, hcy])⟩, fun x hx => ?_⟩
        rw [Mass0.toRat_le, hc]
        exact hlow ⟨_, (hS x).1 hx, rfl⟩
    have hface : ∀ x, (S x ∧ c x = L) ↔ Idx.map Mass0.toRat x ∈ {y | y ∈ S' ∧ c' y = L.toRat} := fun x => by
      show _ ↔ (Idx.map Mass0.toRat x ∈ S' ∧ c' (Idx.map Mass0.toRat x) = L.toRat)
      rw [← hS, ← hc, Mass0.toRat_eq]
    have hface0 : ∀ y ∈ {y | y ∈ S' ∧ c' y = L.toRat}, ∀ i, 0 ≤ y i := fun y hy => hS0 y hy.1
    constructor
    · rintro ⟨hP, d, hd, hm⟩
      have hne : ({y | y ∈ S' ∧ c' y = L.toRat} : Set _).Nonempty := by
        obtain ⟨x, hx, hcx⟩ := hP.1
        exact ⟨_, (hface x).1 ⟨hx, hcx⟩⟩
      refine ⟨L.toNNRat, by rw [Mass0.coe_toNNRat]; exact hL.1 hP, ?_⟩
      rw [Mass0.coe_toNNRat, ← (faceDim_iff _ _ hface hface0 hne d).1 hd]
      rw [Count0.toNat_eq, Count0.toNat_of, Count0.toNat_add, Count0.toNat_one] at hm
      rw [hm, Nat.add_sub_cancel]
    · rintro ⟨L', hL', he⟩
      obtain ⟨h1, h2⟩ := QppMathlib.Pair.mk_eq.1 he
      subst h1
      rw [Mass0.coe_toNNRat] at hL' h2
      have hP := hL.2 hL'
      have hne : ({y | y ∈ S' ∧ c' y = L.toRat} : Set _).Nonempty := by
        obtain ⟨x, hx, hcx⟩ := hP.1
        exact ⟨_, (hface x).1 ⟨hx, hcx⟩⟩
      refine ⟨hP, Count0.ofNat (m.toNat - 1), (faceDim_iff _ _ hface hface0 hne _).2 ?_, ?_⟩
      · rw [Count0.toNat_ofNat]; exact h2
      · rw [Count0.toNat_eq, Count0.toNat_of, Count0.toNat_add, Count0.toNat_one, Count0.toNat_ofNat]
        have := Count.toNat_pos m; omega

/-- `isProg_iff` with the feasible set of Mathlib given by its predicate `p`, as a generated program states it: the
side conditions read `p` at a point, with no membership. -/
theorem isProg_iff_pred (S : (Idx k → Mass0) → Prop) (c : (Idx k → Mass0) → Mass0)
    (p : (Fin k.toNat → ℚ) → Prop) (c' : (Fin k.toNat → ℚ) → ℚ)
    (hS : ∀ x, S x ↔ p (Idx.map Mass0.toRat x)) (hS0 : ∀ y, p y → ∀ i, 0 ≤ y i)
    (hc : ∀ x, (c x).toRat = c' (Idx.map Mass0.toRat x)) (P : PairLM) :
    IsProg S c P ↔ QppMathlib.Pair.IsProg {y | p y} c' P.toMath :=
  isProg_iff S c {y | p y} c' hS hS0 hc P

end Qpp
