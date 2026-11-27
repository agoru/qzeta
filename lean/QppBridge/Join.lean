module

public import QppBridge.Box
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# The bridge of two tuples joined

`join x y` (`Idx.join`) has over the kernel only its two defining equations. Its laws are read here through the
counts of its indices (`Count0.toNat_add`): the halves `Idx.fst`, `Idx.snd` of a join are its two tuples, and its
reading at `j : Fin (n + n').toNat` is `Fin.append` of the readings of its tuples, at `j` cast to
`Fin (n.toNat + n'.toNat)`. The tuples of a size `n + n'` are read on `Fin (n.toNat + n'.toNat)`, as the Mathlib
reading at the sizes `n` and `n'` asks. The cited box split (`fact_boxsplit_core`) is read from `Finset.sum_product`.
-/

@[expose] public section

namespace Qpp

open Classical

namespace Idx

/-- The reading of a join at `j : Fin (n + n').toNat`: `Fin.append` of the readings, at `j` cast to
`Fin (n.toNat + n'.toNat)`. -/
theorem join_ofFin {β : Type} [Inhabited β] {n n' : Count0} (x : Idx n → β) (y : Idx n' → β)
    (j : Fin (n + n').toNat) :
    Idx.join x y (ofFin j) =
      Fin.append (fun i => x (ofFin i)) (fun i => y (ofFin i)) (Fin.cast (Count0.toNat_add n n') j) := by
  by_cases hj : j.1 < n.toNat
  · have h : Count0.of (ofFin j).1 ≤ n := by
      rw [Count0.toNat_le, Count0.toNat_of, toNat_ofFin]; omega
    rw [Idx.join_left x y _ h]
    have e : Fin.cast (Count0.toNat_add n n') j = Fin.castAdd n'.toNat ⟨j.1, hj⟩ := Fin.ext rfl
    rw [e, Fin.append_left]
    rfl
  · have h : ¬ Count0.of (ofFin j).1 ≤ n := by
      rw [Count0.toNat_le, Count0.toNat_of, toNat_ofFin]; omega
    have hlt : j.1 - n.toNat < n'.toNat := by have := j.2; have := Count0.toNat_add n n'; omega
    have ex : ∃ k : Idx n', Count0.of (ofFin j).1 = n + Count0.of k.1 := by
      refine ⟨ofFin ⟨j.1 - n.toNat, hlt⟩, ?_⟩
      rw [Count0.toNat_eq, Count0.toNat_add, Count0.toNat_of, Count0.toNat_of, toNat_ofFin, toNat_ofFin]
      dsimp only; omega
    rw [Idx.join_right x y _ h ex]
    have hc := Classical.choose_spec ex
    have hk : Classical.choose ex = ofFin ⟨j.1 - n.toNat, hlt⟩ := by
      rw [← ofFin_toFin (Classical.choose ex), ofFin_eq]
      apply Fin.ext
      rw [Count0.toNat_eq, Count0.toNat_add, Count0.toNat_of, Count0.toNat_of, toNat_ofFin] at hc
      simp only [toFin]; omega
    have e : Fin.cast (Count0.toNat_add n n') j = Fin.natAdd n.toNat ⟨j.1 - n.toNat, hlt⟩ := by
      apply Fin.ext; simp only [Fin.val_cast, Fin.val_natAdd]; omega
    rw [hk, e, Fin.append_right]

/-- The first half of a join is its first tuple. -/
@[qpp_bridge] theorem fst_join {β : Type} [Inhabited β] {n n' : Count0} (x : Idx n → β) (y : Idx n' → β) :
    Idx.fst (Idx.join x y) = x := by
  funext i
  have h : Count0.of i.1 ≤ n + n' := by
    have := Count0.toNat_le.mp i.2; rw [Count0.toNat_le, Count0.toNat_add]; omega
  unfold Idx.fst Idx.extend
  simp only [h, ↓reduceDIte]
  exact Idx.join_left x y ⟨i.1, h⟩ i.2

/-- The second half of a join is its second tuple. -/
@[qpp_bridge] theorem snd_join {β : Type} [Inhabited β] {n n' : Count0} (x : Idx n → β) (y : Idx n' → β) :
    Idx.snd (Idx.join x y) = y := by
  funext j
  have hj := Count0.toNat_le.mp j.2
  have h : Count0.of (n + j.1) ≤ n + n' := by
    rw [Count0.toNat_le, Count0.toNat_add, Count0.toNat_of, Count.toNat_add0']; rw [Count0.toNat_of] at hj; omega
  unfold Idx.snd Idx.extend
  simp only [h, ↓reduceDIte]
  have hn : ¬ Count0.of (n + j.1) ≤ n := by
    rw [Count0.toNat_le, Count0.toNat_of, Count.toNat_add0']; have := Count.toNat_pos j.1; omega
  have ex : ∃ k : Idx n', Count0.of (n + j.1) = n + Count0.of k.1 := ⟨j, by
    rw [Count0.toNat_eq, Count0.toNat_add, Count0.toNat_of, Count0.toNat_of, Count.toNat_add0']⟩
  refine (Idx.join_right x y ⟨n + j.1, h⟩ hn ex).trans (congrArg y ?_)
  have hc := Classical.choose_spec ex
  apply Subtype.ext; apply Count.toNat_inj
  rw [Count0.toNat_eq, Count0.toNat_add, Count0.toNat_of, Count0.toNat_of, Count.toNat_add0'] at hc
  omega

/-! ## The readings at a size `n + n'`

The Mathlib reading of a statement at the sizes `n` and `n'` asks its tuples of `n + n'` coordinates on
`Fin (n.toNat + n'.toNat)`, while an index of `Idx (n + n')` is read on `Fin (n + n').toNat`. The two are the same
by `Count0.toNat_add`, through `Fin.cast`: an index, a tuple, a quantifier, a sum and a box of the size `n + n'` are
read on `Fin (n.toNat + n'.toNat)`. These readings are the simp set `qpp_bridge_add`, which the transfer of a
statement with such a size adds; there they come before those at a size `n` (priority `high`). -/

/-- The index of `j : Fin (n.toNat + n'.toNat)` in `Idx (n + n')`. -/
def ofFinAdd {n n' : Count0} (j : Fin (n.toNat + n'.toNat)) : Idx (n + n') :=
  ofFin (Fin.cast (Count0.toNat_add n n').symm j)

/-- The index `i` of `Idx (n + n')` on `Fin (n.toNat + n'.toNat)`. -/
def toFinAdd {n n' : Count0} (i : Idx (n + n')) : Fin (n.toNat + n'.toNat) :=
  Fin.cast (Count0.toNat_add n n') (toFin i)

/-- The reading of a tuple of `n + n'` entries on `Fin (n.toNat + n'.toNat)`. -/
def mapAdd {n n' : Count0} {X Y : Type} (φ : X → Y) (u : Idx (n + n') → X) : Fin (n.toNat + n'.toNat) → Y :=
  fun j => φ (u (ofFinAdd j))

/-- The tuple of `n + n'` entries of a function on `Fin (n.toNat + n'.toNat)`. -/
def unmapAdd {n n' : Count0} {X Y : Type} (ψ : Y → X) (v : Fin (n.toNat + n'.toNat) → Y) : Idx (n + n') → X :=
  fun i => ψ (v (toFinAdd i))

@[qpp_bridge] theorem toFinAdd_ofFinAdd {n n' : Count0} (j : Fin (n.toNat + n'.toNat)) :
    toFinAdd (ofFinAdd j) = j := by
  unfold toFinAdd ofFinAdd; rw [toFin_ofFin]; rfl

@[qpp_bridge] theorem ofFinAdd_toFinAdd {n n' : Count0} (i : Idx (n + n')) : ofFinAdd (toFinAdd i) = i := by
  unfold toFinAdd ofFinAdd
  have e : Fin.cast (Count0.toNat_add n n').symm (Fin.cast (Count0.toNat_add n n') (toFin i)) = toFin i := rfl
  rw [e, ofFin_toFin]

@[qpp_bridge_add high] theorem forall_add_iff {n n' : Count0} {P : Idx (n + n') → Prop} :
    (∀ i, P i) ↔ ∀ j : Fin (n.toNat + n'.toNat), P (ofFinAdd j) :=
  ⟨fun h j => h _, fun h i => by rw [← ofFinAdd_toFinAdd i]; exact h _⟩

@[qpp_bridge_add high] theorem exists_add_iff {n n' : Count0} {P : Idx (n + n') → Prop} :
    (∃ i, P i) ↔ ∃ j : Fin (n.toNat + n'.toNat), P (ofFinAdd j) :=
  ⟨fun ⟨i, h⟩ => ⟨toFinAdd i, by rwa [ofFinAdd_toFinAdd]⟩, fun ⟨j, h⟩ => ⟨_, h⟩⟩

@[qpp_bridge] theorem toNat_ofFinAdd {n n' : Count0} (j : Fin (n.toNat + n'.toNat)) :
    (ofFinAdd j).1.toNat = j.1 + 1 := by
  unfold ofFinAdd; rw [toNat_ofFin]; rfl

@[qpp_bridge] theorem ofFinAdd_eq {n n' : Count0} {j j' : Fin (n.toNat + n'.toNat)} :
    ofFinAdd j = ofFinAdd j' ↔ j = j' :=
  ⟨fun h => by rw [← toFinAdd_ofFinAdd j, h, toFinAdd_ofFinAdd], fun h => h ▸ rfl⟩

@[qpp_bridge] theorem ofFinAdd_lt {n n' : Count0} {j j' : Fin (n.toNat + n'.toNat)} :
    ofFinAdd j < ofFinAdd j' ↔ j < j' := by
  show (ofFinAdd j).1 < (ofFinAdd j').1 ↔ _
  rw [Count.toNat_lt, toNat_ofFinAdd, toNat_ofFinAdd, Fin.lt_def]; omega

@[qpp_bridge] theorem ofFinAdd_le {n n' : Count0} {j j' : Fin (n.toNat + n'.toNat)} :
    ofFinAdd j ≤ ofFinAdd j' ↔ j ≤ j' := by
  show (ofFinAdd j).1 ≤ (ofFinAdd j').1 ↔ _
  rw [Count.toNat_le, toNat_ofFinAdd, toNat_ofFinAdd, Fin.le_iff_val_le_val]; omega

@[qpp_bridge] theorem mapAdd_apply {n n' : Count0} {X Y : Type} (φ : X → Y) (u : Idx (n + n') → X)
    (j : Fin (n.toNat + n'.toNat)) : mapAdd φ u j = φ (u (ofFinAdd j)) := rfl

@[qpp_bridge] theorem unmapAdd_apply {n n' : Count0} {X Y : Type} (ψ : Y → X) (v : Fin (n.toNat + n'.toNat) → Y)
    (i : Idx (n + n')) : unmapAdd ψ v i = ψ (v (toFinAdd i)) := rfl

theorem unmapAdd_mapAdd {n n' : Count0} {X Y : Type} (φ : X → Y) (ψ : Y → X) (h : ∀ x, ψ (φ x) = x)
    (u : Idx (n + n') → X) : unmapAdd ψ (mapAdd φ u) = u := by
  funext i; rw [unmapAdd_apply, mapAdd_apply, ofFinAdd_toFinAdd, h]

theorem mapAdd_unmapAdd {n n' : Count0} {X Y : Type} (φ : X → Y) (ψ : Y → X) (h : ∀ y, φ (ψ y) = y)
    (v : Fin (n.toNat + n'.toNat) → Y) : mapAdd φ (unmapAdd ψ v) = v := by
  funext j; rw [mapAdd_apply, unmapAdd_apply, toFinAdd_ofFinAdd, h]

theorem forall_readAdd {n n' : Count0} {X Y : Type} (φ : X → Y) (ψ : Y → X) (h : ∀ x, ψ (φ x) = x)
    {P : (Idx (n + n') → X) → Prop} : (∀ x, P x) ↔ ∀ y : Fin (n.toNat + n'.toNat) → Y, P (unmapAdd ψ y) :=
  ⟨fun hP _ => hP _, fun hP x => by rw [← unmapAdd_mapAdd φ ψ h x]; exact hP _⟩

theorem exists_readAdd {n n' : Count0} {X Y : Type} (φ : X → Y) (ψ : Y → X) (h : ∀ x, ψ (φ x) = x)
    {P : (Idx (n + n') → X) → Prop} : (∃ x, P x) ↔ ∃ y : Fin (n.toNat + n'.toNat) → Y, P (unmapAdd ψ y) :=
  ⟨fun ⟨x, hx⟩ => ⟨mapAdd φ x, by rwa [unmapAdd_mapAdd φ ψ h x]⟩, fun ⟨_, hy⟩ => ⟨_, hy⟩⟩

@[qpp_bridge_add high] theorem forall_count0_add {n n' : Count0} {P : (Idx (n + n') → Count0) → Prop} :
    (∀ x, P x) ↔ ∀ y : Fin (n.toNat + n'.toNat) → ℕ, P (unmapAdd Count0.ofNat y) :=
  forall_readAdd Count0.toNat Count0.ofNat Count0.ofNat_toNat

@[qpp_bridge_add high] theorem exists_count0_add {n n' : Count0} {P : (Idx (n + n') → Count0) → Prop} :
    (∃ x, P x) ↔ ∃ y : Fin (n.toNat + n'.toNat) → ℕ, P (unmapAdd Count0.ofNat y) :=
  exists_readAdd Count0.toNat Count0.ofNat Count0.ofNat_toNat

@[qpp_bridge_add high] theorem forall_mass0_add {n n' : Count0} {P : (Idx (n + n') → Mass0) → Prop} :
    (∀ x, P x) ↔ ∀ y : Fin (n.toNat + n'.toNat) → ℚ≥0, P (unmapAdd Mass0.ofNNRat y) :=
  forall_readAdd Mass0.toNNRat Mass0.ofNNRat Mass0.ofNNRat_toNNRat

@[qpp_bridge_add high] theorem exists_mass0_add {n n' : Count0} {P : (Idx (n + n') → Mass0) → Prop} :
    (∃ x, P x) ↔ ∃ y : Fin (n.toNat + n'.toNat) → ℚ≥0, P (unmapAdd Mass0.ofNNRat y) :=
  exists_readAdd Mass0.toNNRat Mass0.ofNNRat Mass0.ofNNRat_toNNRat

/-- A quantifier over the functions on the tuples of counts of a size `n + n'`, valued in the masses or absent. -/
@[qpp_bridge_add high] theorem forall_fun_count0_add {n n' : Count0} {P : ((Idx (n + n') → Count0) → Mass0) → Prop} :
    (∀ G, P G) ↔
      ∀ H : (Fin (n.toNat + n'.toNat) → ℕ) → ℚ≥0, P (fun u => Mass0.ofNNRat (H (mapAdd Count0.toNat u))) := by
  refine ⟨fun h _ => h _, fun h G => ?_⟩
  have e : (fun u => Mass0.ofNNRat ((fun v => Mass0.toNNRat (G (unmapAdd Count0.ofNat v)))
      (mapAdd Count0.toNat u))) = G := by
    funext u; simp only [unmapAdd_mapAdd Count0.toNat Count0.ofNat Count0.ofNat_toNat, Mass0.ofNNRat_toNNRat]
  rw [← e]; exact h (fun v => Mass0.toNNRat (G (unmapAdd Count0.ofNat v)))

@[qpp_bridge_add high] theorem exists_fun_count0_add {n n' : Count0} {P : ((Idx (n + n') → Count0) → Mass0) → Prop} :
    (∃ G, P G) ↔
      ∃ H : (Fin (n.toNat + n'.toNat) → ℕ) → ℚ≥0, P (fun u => Mass0.ofNNRat (H (mapAdd Count0.toNat u))) := by
  refine ⟨fun ⟨G, hG⟩ => ⟨fun v => Mass0.toNNRat (G (unmapAdd Count0.ofNat v)), ?_⟩, fun ⟨_, h⟩ => ⟨_, h⟩⟩
  have e : (fun u => Mass0.ofNNRat ((fun v => Mass0.toNNRat (G (unmapAdd Count0.ofNat v)))
      (mapAdd Count0.toNat u))) = G := by
    funext u; simp only [unmapAdd_mapAdd Count0.toNat Count0.ofNat Count0.ofNat_toNat, Mass0.ofNNRat_toNNRat]
  rw [e]; exact hG

@[qpp_bridge] theorem unmapAdd_mapAdd_count0 {n n' : Count0} (x : Idx (n + n') → Count0) :
    unmapAdd Count0.ofNat (mapAdd Count0.toNat x) = x :=
  unmapAdd_mapAdd Count0.toNat Count0.ofNat Count0.ofNat_toNat x

@[qpp_bridge] theorem unmapAdd_mapAdd_mass0 {n n' : Count0} (x : Idx (n + n') → Mass0) :
    unmapAdd Mass0.ofNNRat (mapAdd Mass0.toNNRat x) = x :=
  unmapAdd_mapAdd Mass0.toNNRat Mass0.ofNNRat Mass0.ofNNRat_toNNRat x

@[qpp_bridge] theorem mapAdd_unmapAdd_count0 {n n' : Count0} (y : Fin (n.toNat + n'.toNat) → ℕ) :
    mapAdd Count0.toNat (unmapAdd Count0.ofNat y) = y :=
  mapAdd_unmapAdd _ _ Count0.toNat_ofNat y

@[qpp_bridge] theorem mapAdd_unmapAdd_mass0 {n n' : Count0} (y : Fin (n.toNat + n'.toNat) → ℚ≥0) :
    mapAdd Mass0.toNNRat (unmapAdd Mass0.ofNNRat y) = y :=
  mapAdd_unmapAdd _ _ Mass0.toNNRat_ofNNRat y

/-- The reading of a join at `j : Fin (n.toNat + n'.toNat)`: `Fin.append` of the readings. -/
theorem join_ofFinAdd {β : Type} [Inhabited β] {n n' : Count0} (x : Idx n → β) (y : Idx n' → β)
    (j : Fin (n.toNat + n'.toNat)) :
    Idx.join x y (ofFinAdd j) = Fin.append (fun i => x (ofFin i)) (fun i => y (ofFin i)) j := by
  unfold ofFinAdd; rw [join_ofFin]; rfl

@[qpp_bridge] theorem mapAdd_join {β γ : Type} [Inhabited β] {n n' : Count0} (φ : β → γ) (x : Idx n → β)
    (y : Idx n' → β) : mapAdd φ (Idx.join x y) = Fin.append (map φ x) (map φ y) := by
  funext j
  rw [mapAdd_apply, join_ofFinAdd]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [Fin.append_left, map_apply]
  · simp only [Fin.append_right, map_apply]

@[qpp_bridge] theorem unmapAdd_append {β γ : Type} [Inhabited β] {n n' : Count0} (ψ : γ → β)
    (u : Fin n.toNat → γ) (v : Fin n'.toNat → γ) :
    unmapAdd ψ (Fin.append u v) = Idx.join (unmap ψ u) (unmap ψ v) := by
  funext i
  rw [← ofFinAdd_toFinAdd i, join_ofFinAdd, unmapAdd_apply, toFinAdd_ofFinAdd]
  refine Fin.addCases (fun k => ?_) (fun k => ?_) (toFinAdd i)
  · simp only [Fin.append_left, unmap_apply, toFin_ofFin]
  · simp only [Fin.append_right, unmap_apply, toFin_ofFin]

/-- A sum over `Fin m` reindexed on `Fin m'` by `m = m'`, and a sum over a box. -/
theorem sum_fin_cast {γ : Type} [AddCommMonoid γ] {m m' : ℕ} (h : m = m') (f : Fin m → γ) :
    ∑ j : Fin m, f j = ∑ j : Fin m', f (Fin.cast h.symm j) := by
  subst h; rfl

theorem prod_fin_cast {γ : Type} [CommMonoid γ] {m m' : ℕ} (h : m = m') (f : Fin m → γ) :
    ∏ j : Fin m, f j = ∏ j : Fin m', f (Fin.cast h.symm j) := by
  subst h; rfl

theorem sum_box_cast {γ : Type} [AddCommMonoid γ] {m m' : ℕ} (h : m = m') (v : Fin m → ℕ) (F : (Fin m → ℕ) → γ) :
    ∑ u ∈ Finset.Icc 0 v, F u = ∑ u ∈ Finset.Icc 0 (fun j => v (Fin.cast h.symm j)), F (fun j => u (Fin.cast h j)) := by
  subst h; rfl

end Idx

@[qpp_bridge_add high] theorem Mass0.toRat_idxSum_add (n n' : Count0) (f : Idx (n + n') → Mass0) :
    (Idx.sum (n + n') f).toRat = ∑ j : Fin (n.toNat + n'.toNat), (f (Idx.ofFinAdd j)).toRat := by
  rw [Mass0.toRat_idxSum, Idx.sum_fin_cast (Count0.toNat_add n n')]; rfl

@[qpp_bridge_add high] theorem Count0.toNat_idxSum_add (n n' : Count0) (f : Idx (n + n') → Count0) :
    (Idx.sum (n + n') f).toNat = ∑ j : Fin (n.toNat + n'.toNat), (f (Idx.ofFinAdd j)).toNat := by
  rw [Count0.toNat_idxSum, Idx.sum_fin_cast (Count0.toNat_add n n')]; rfl

@[qpp_bridge_add high] theorem Mass0.toRat_idxProd_add (n n' : Count0) (f : Idx (n + n') → Mass0) :
    (Idx.prod (n + n') f).toRat = ∏ j : Fin (n.toNat + n'.toNat), (f (Idx.ofFinAdd j)).toRat := by
  rw [Mass0.toRat_idxProd, Idx.prod_fin_cast (Count0.toNat_add n n')]; rfl

@[qpp_bridge_add high] theorem Count0.toNat_idxProd_add (n n' : Count0) (f : Idx (n + n') → Count0) :
    (Idx.prod (n + n') f).toNat = ∏ j : Fin (n.toNat + n'.toNat), (f (Idx.ofFinAdd j)).toNat := by
  rw [Count0.toNat_idxProd, Idx.prod_fin_cast (Count0.toNat_add n n')]; rfl

@[qpp_bridge_add high] theorem Mass0.toRat_boxSum_add (n n' : Count0) (b : Idx (n + n') → Count0)
    (f : (Idx (n + n') → Count0) → Mass0) :
    (boxSum (n + n') b f).toRat =
      ∑ u ∈ Finset.Icc 0 (Idx.mapAdd Count0.toNat b), (f (Idx.unmapAdd Count0.ofNat u)).toRat := by
  rw [Mass0.toRat_boxSum, Idx.sum_box_cast (Count0.toNat_add n n')]; rfl

@[qpp_bridge_add high] theorem Count0.toNat_boxSum_add (n n' : Count0) (b : Idx (n + n') → Count0)
    (f : (Idx (n + n') → Count0) → Count0) :
    (boxSum (n + n') b f).toNat =
      ∑ u ∈ Finset.Icc 0 (Idx.mapAdd Count0.toNat b), (f (Idx.unmapAdd Count0.ofNat u)).toNat := by
  rw [Count0.toNat_boxSum, Idx.sum_box_cast (Count0.toNat_add n n')]; rfl

end Qpp

namespace Qpp.Cite

open Finset

/-- Two joined tuples compare as their halves do. -/
theorem fin_append_le_iff {n n' : ℕ} (u b : Fin n → ℕ) (w c : Fin n' → ℕ) :
    Fin.append u w ≤ Fin.append b c ↔ u ≤ b ∧ w ≤ c := by
  constructor
  · intro h
    exact ⟨fun i => by simpa using h (Fin.castAdd n' i), fun j => by simpa using h (Fin.natAdd n j)⟩
  · rintro ⟨hu, hw⟩ k
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simpa using hu i
    · simpa using hw j

/-- The box of a join is the product of its two boxes (`fact:boxsplit`): Mathlib `Finset.sum_product`, at the
bijection `Fin.append` of the pairs of points of the two boxes onto the box of the join (`Finset.sum_nbij'`). -/
theorem fact_boxsplit_core :
    ∀ (n n' : ℕ) (b : Fin n → ℕ) (c : Fin n' → ℕ) (G : (Fin (n + n') → ℕ) → ℚ≥0),
      (∑ z ∈ Finset.Icc 0 (Fin.append b c), (G z : ℚ)) =
        (∑ w ∈ Finset.Icc 0 c, (∑ u ∈ Finset.Icc 0 b, (G (Fin.append u w) : ℚ))) := by
  intro n n' b c G
  rw [Finset.sum_comm]
  have hp := Finset.sum_product (Finset.Icc 0 b) (Finset.Icc 0 c) (fun x => (G (Fin.append x.1 x.2) : ℚ))
  simp only at hp
  rw [← hp]
  symm
  refine Finset.sum_nbij' (fun x => Fin.append x.1 x.2)
    (fun z => (fun i => z (Fin.castAdd n' i), fun j => z (Fin.natAdd n j))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨u, w⟩ hx
    simp only [Finset.mem_product, Finset.mem_Icc] at hx
    simp only [Finset.mem_Icc]
    refine ⟨(fun _ => Nat.zero_le _), (fin_append_le_iff u b w c).2 ⟨hx.1.2, hx.2.2⟩⟩
  · intro z hz
    simp only [Finset.mem_Icc] at hz
    simp only [Finset.mem_product, Finset.mem_Icc]
    have e : z = Fin.append (fun i => z (Fin.castAdd n' i)) (fun j => z (Fin.natAdd n j)) := by
      funext k; refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp
    rw [e] at hz
    have := (fin_append_le_iff _ b _ c).1 hz.2
    exact ⟨⟨(fun _ => Nat.zero_le _), this.1⟩, ⟨(fun _ => Nat.zero_le _), this.2⟩⟩
  · rintro ⟨u, w⟩ _
    simp
  · intro z _
    funext k; refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp
  · intro x _; rfl

end Qpp.Cite
