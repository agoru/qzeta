module

public import QppBridge.Sums

/-!
# The bridge of sums over a box

`sum u <= b, f u` (`boxSum`) is read as the sum over `Finset.Icc 0 b` of `Fin n → ℕ`, the Mathlib reading: a lattice
point `u : Fin n → ℕ` is the tuple `Idx.unmap Count0.ofNat u`. The kernel sums the last coordinate outermost
(`boxTo`); Mathlib's box is the product of its coordinate intervals (`Pi.Icc_eq`), split at the last coordinate by
`Fin.snocEquiv`.
-/

@[expose] public section

namespace Qpp

open Classical Finset

section Box

variable {β γ : Type}

/-- A lattice point `u : Fin N → ℕ` as a function on every count, absent beyond `N`. -/
noncomputable def extN {N : ℕ} (u : Fin N → ℕ) (i : Count) : Count0 :=
  if h : i.toNat - 1 < N then Count0.ofNat (u ⟨i.toNat - 1, h⟩) else 0

theorem sum_piFinset_snoc [AddCommMonoid γ] {N : ℕ} (S : Fin (N + 1) → Finset ℕ) (F : (Fin (N + 1) → ℕ) → γ) :
    ∑ u ∈ Fintype.piFinset S, F u =
      ∑ v ∈ S (Fin.last N), ∑ w ∈ Fintype.piFinset (Fin.init S), F (Fin.snoc w v) := by
  have h := Finset.filter_piFinset_eq_map_snocEquiv (α := fun _ => ℕ) S (fun _ => True)
  rw [Finset.filter_true_of_mem (fun _ _ => trivial), Finset.filter_true_of_mem (fun _ _ => trivial)] at h
  rw [h, Finset.sum_map, Finset.sum_product]
  rfl

theorem extN_snoc {N : ℕ} (w : Fin N → ℕ) (v : ℕ) (c : Count) (hc : c.toNat = N) :
    extN (Fin.snoc w v : Fin (N + 1) → ℕ) = fun i => if i = Count.succ c then Count0.ofNat v else extN w i := by
  funext i
  have hi := Count.toNat_pos i
  by_cases e : i = Count.succ c
  · subst e
    have h1 : (Count.succ c).toNat - 1 = N := by rw [Count.toNat_succ']; omega
    rw [ite_eq_left rfl]; unfold extN
    rw [dite_eq_left (by omega)]
    have : (⟨(Count.succ c).toNat - 1, by omega⟩ : Fin (N + 1)) = Fin.last N := Fin.ext h1
    rw [this, Fin.snoc_last]
  · rw [ite_eq_right e]
    have hne : i.toNat ≠ c.toNat + 1 := fun h => e (Count.toNat_inj (by rw [h, Count.toNat_succ']))
    by_cases hlt : i.toNat - 1 < N
    · simp only [extN, dite_eq_left hlt, dite_eq_left (show i.toNat - 1 < N + 1 by omega)]
      have : (⟨i.toNat - 1, by omega⟩ : Fin (N + 1)) = Fin.castSucc ⟨i.toNat - 1, hlt⟩ := rfl
      rw [this, Fin.snoc_castSucc]
    · simp only [extN, dite_eq_right hlt, dite_eq_right (show ¬ i.toNat - 1 < N + 1 by omega)]

theorem extN_one (v : ℕ) (w : Fin 0 → ℕ) :
    extN (Fin.snoc w v : Fin 1 → ℕ) = fun i => if i = 1 then Count0.ofNat v else 0 := by
  funext i
  have hi := Count.toNat_pos i
  by_cases e : i = 1
  · subst e
    rw [ite_eq_left rfl]; unfold extN
    rw [dite_eq_left (show (1 : Count).toNat - 1 < 1 from Nat.zero_lt_one)]
    have : (⟨(1 : Count).toNat - 1, Nat.zero_lt_one⟩ : Fin 1) = Fin.last 0 := Fin.ext rfl
    rw [this, Fin.snoc_last]
  · rw [ite_eq_right e]
    have : i.toNat ≠ 1 := fun h => e (Count.toNat_inj (by rw [h, Count.toNat_one']))
    simp only [extN, dite_eq_right (show ¬ i.toNat - 1 < 1 by omega)]

theorem map_boxTo [Add β] [AddCommMonoid γ] (φ : β → γ) (hφ : ∀ a b, φ (a + b) = φ a + φ b)
    (B : Count → Count0) (c : Count) (F : (Count → Count0) → β) :
    φ (boxTo B c F) =
      ∑ u ∈ Fintype.piFinset (fun j : Fin c.toNat => Icc 0 (B (Count.ofNatSucc j.1)).toNat), φ (F (extN u)) := by
  induction c using Count.ind generalizing F with
  | h1 =>
    show φ (upTo (B 1) _) =
      ∑ u ∈ Fintype.piFinset (fun j : Fin (0 + 1) => Icc 0 (B (Count.ofNatSucc j.1)).toNat), φ (F (extN u))
    rw [map_upTo φ hφ, sum_piFinset_snoc]
    refine Finset.sum_congr rfl fun v _ => ?_
    have h0 : Fintype.piFinset (Fin.init fun j : Fin (0 + 1) => Icc 0 (B (Count.ofNatSucc j.1)).toNat) =
        {Fin.elim0} := by
      ext w; simp only [Fintype.mem_piFinset, Finset.mem_singleton]
      exact ⟨fun _ => Subsingleton.elim _ _, fun _ i => i.elim0⟩
    rw [h0, Finset.sum_singleton, extN_one]
  | hs c ih =>
    show φ (upTo (B (Count.succ c)) _) =
      ∑ u ∈ Fintype.piFinset (fun j : Fin (c.toNat + 1) => Icc 0 (B (Count.ofNatSucc j.1)).toNat), φ (F (extN u))
    rw [map_upTo φ hφ, sum_piFinset_snoc]
    simp only [Fin.val_last, ofNatSucc_toNat]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [ih]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [extN_snoc w v c rfl]

theorem idx_none_elim (i : Idx 0) : False := by
  have := i.toNat_le; have := Count.toNat_pos i.1; exact absurd this (by simp [Count0.toNat] at *; omega)

/-- Cases on a count or absent, with the cases typed as counts or absent. -/
@[elab_as_elim] theorem Count0.cases' {motive : Count0 → Prop} (h0 : motive 0) (hs : ∀ c, motive (Count0.of c))
    (n : Count0) : motive n := by
  cases n with
  | none => exact h0
  | some c => exact hs c

theorem map_boxSum [Add β] [AddCommMonoid γ] (φ : β → γ) (hφ : ∀ a b, φ (a + b) = φ a + φ b)
    (n : Count0) (b : Idx n → Count0) (f : (Idx n → Count0) → β) :
    φ (boxSum n b f) = ∑ u ∈ Icc 0 (Idx.map Count0.toNat b), φ (f (Idx.unmap Count0.ofNat u)) := by
  induction n using Count0.cases' with
  | h0 =>
    show φ (f fun _ => 0) = _
    have hb : Idx.map Count0.toNat b = 0 := funext fun j => (Nat.not_lt_zero _ j.2).elim
    rw [hb, Icc_self, sum_singleton]
    congr 2
  | hs c =>
    show φ (boxTo (Idx.extend 0 b) c _) = _
    rw [map_boxTo φ hφ, Pi.Icc_eq]
    have hS : (fun j : Fin c.toNat => Icc 0 (Idx.extend 0 b (Count.ofNatSucc j.1)).toNat) =
        fun j => Icc ((0 : Fin c.toNat → ℕ) j) (Idx.map Count0.toNat b j) := by
      funext j; exact congrArg (fun x => Icc 0 (Count0.toNat x)) (Idx.extend_ofNatSucc _ b j)
    rw [hS]
    refine Finset.sum_congr rfl fun u _ => ?_
    congr 2; funext i
    have hi := Idx.toNat_le i; have := Count.toNat_pos i.1
    show extN u i.1 = Count0.ofNat (u (Idx.toFin i))
    simp only [extN, dite_eq_left (show i.1.toNat - 1 < c.toNat by exact Nat.sub_one_lt_of_le this hi)]
    rfl

end Box

@[qpp_bridge] theorem Mass0.toRat_boxSum (n : Count0) (b : Idx n → Count0) (f : (Idx n → Count0) → Mass0) :
    (boxSum n b f).toRat = ∑ u ∈ Icc 0 (Idx.map Count0.toNat b), (f (Idx.unmap Count0.ofNat u)).toRat :=
  map_boxSum _ Mass0.toRat_add n b f

@[qpp_bridge] theorem Count0.toNat_boxSum (n : Count0) (b : Idx n → Count0) (f : (Idx n → Count0) → Count0) :
    (boxSum n b f).toNat = ∑ u ∈ Icc 0 (Idx.map Count0.toNat b), (f (Idx.unmap Count0.ofNat u)).toNat :=
  map_boxSum _ Count0.toNat_add n b f

end Qpp
