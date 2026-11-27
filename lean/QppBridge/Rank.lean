module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The readings of the cited facts of linear algebra over the rationals

A cited fact of `theory` is stated on rows and points with natural entries, with a quantity of both signs given as
two positive parts (a balance) and an identity of both signs as a tie of two positive sums. This file reads each
statement from the Mathlib lemmas of linear algebra over `ℚ` that prove it, once. Each statement is the generated
one; a rational is the difference of its positive part and its deficit (`toNNRat_sub_neg`).

- `fact_dual_core`: barycentric coordinates of affinely independent points. Mathlib
  `Matrix.mulVec_surjective_iff_rank_eq_card`: the points with a last coordinate `1` are the rows of a matrix whose
  rows are linearly independent, so that its `mulVec` is onto; the preimage of the unit vector at `κ` is the
  coordinate function of the point `κ`.
- `fact_basis_core`: rank and nullity, on a basis of rows. Mathlib `LinearMap.finrank_range_add_finrank_ker`, with
  `exists_linearIndependent` and `exists_linearIndepOn_id_extension`: rows that span `ℚ^m` contain a basis that
  extends a basis of the rows of the part `I`; the rows of `I` span a space whose dimension is `m` less the
  dimension of the vectors on which they vanish, which lie in the directions of `r = d + 1` points, so that at most
  `d` members of the basis are outside `I`. The basis is an invertible matrix (`Matrix.linearIndependent_row_iff_isUnit`,
  `Matrix.nonsing_inv_mul`), whose inverse gives each coordinate.
-/

@[expose] public section

namespace Qpp.Cite

open Matrix Module Submodule

/-- A rational is the difference of its positive part and its deficit. -/
theorem toNNRat_sub_neg (x : ℚ) : ((x.toNNRat : ℚ) - ((-x).toNNRat : ℚ)) = x := by
  rcases le_total 0 x with h | h
  · rw [Rat.coe_toNNRat x h, (Rat.toNNRat_eq_zero (q := -x)).mpr (by linarith)]; simp
  · rw [(Rat.toNNRat_eq_zero (q := x)).mpr h, Rat.coe_toNNRat (-x) (by linarith)]; simp

/-- Barycentric coordinates: points that are affinely independent, as a tie of two positive weights, have affine
coordinate functions, each a balance. The points with a last coordinate `1` are the rows of a matrix with linearly
independent rows, whose `mulVec` is onto (`Matrix.mulVec_surjective_iff_rank_eq_card`); the preimage of a unit
vector is the coordinate function. -/
theorem fact_dual_core :
    ∀ (m r : ℕ) (R : Fin r → Fin m → ℕ), (∀ zP zM : Fin r → NNRat, ((∀ (i : Fin m), (∑ l : Fin r, (zP l : ℚ) * (R l i : ℚ)) = (∑ l : Fin r, (zM l : ℚ) * (R l i : ℚ))) ∧ ((∑ l : Fin r, (zP l : ℚ)) = (∑ l : Fin r, (zM l : ℚ)))) → (∀ (l : Fin r), (zP l : ℚ) = (zM l : ℚ))) → ∃ psiP psiM : Fin r → Fin m → NNRat, ∃ gP gM : Fin r → NNRat, ∀ (kk : Fin r), ∀ z : Fin r → ℕ, (∑ l : Fin r, (z l : ℚ) * ((∑ i : Fin m, (psiP kk i : ℚ) * (R l i : ℚ)) + (gP kk : ℚ))) = (∑ l : Fin r, (z l : ℚ) * ((∑ i : Fin m, (psiM kk i : ℚ) * (R l i : ℚ)) + (gM kk : ℚ))) + (z kk : ℚ) := by
  intro m r R hind
  classical
  let M : Matrix (Fin r) (Option (Fin m)) ℚ := fun l o => o.elim 1 (fun i => (R l i : ℚ))
  have hrow : LinearIndependent ℚ M.row := by
    rw [Fintype.linearIndependent_iff]
    intro g hg l
    have hcoord : ∀ o, ∑ l, g l * M l o = 0 := by
      intro o
      have := congrFun hg o
      simpa [Finset.sum_apply, Matrix.row, smul_eq_mul] using this
    have hsplit : ∀ o, ∑ l, ((g l).toNNRat : ℚ) * M l o = ∑ l, ((-g l).toNNRat : ℚ) * M l o := by
      intro o
      have e : ∑ l, ((g l).toNNRat : ℚ) * M l o - ∑ l, ((-g l).toNNRat : ℚ) * M l o = ∑ l, g l * M l o := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [← sub_mul, toNNRat_sub_neg]
      linarith [hcoord o]
    have h1 := hind (fun l => (g l).toNNRat) (fun l => (-g l).toNNRat)
      ⟨fun i => by simpa [M] using hsplit (some i), by simpa [M] using hsplit none⟩ l
    have := toNNRat_sub_neg (g l)
    linarith
  have hs : Function.Surjective M.mulVec :=
    Matrix.mulVec_surjective_iff_rank_eq_card.mpr hrow.rank_matrix
  choose v hv using fun kk : Fin r => hs (Pi.single kk 1)
  refine ⟨fun kk i => (v kk (some i)).toNNRat, fun kk i => (-v kk (some i)).toNNRat,
    fun kk => (v kk none).toNNRat, fun kk => (-v kk none).toNNRat, ?_⟩
  intro kk z
  have key : ∀ l, ((∑ i, ((v kk (some i)).toNNRat : ℚ) * (R l i : ℚ)) + ((v kk none).toNNRat : ℚ)) -
      ((∑ i, ((-v kk (some i)).toNNRat : ℚ) * (R l i : ℚ)) + ((-v kk none).toNNRat : ℚ)) =
      if l = kk then 1 else 0 := by
    intro l
    have h := congrFun (hv kk) l
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_option, M, Option.elim, one_mul] at h
    rw [Pi.single_apply] at h
    have e : ((∑ i, ((v kk (some i)).toNNRat : ℚ) * (R l i : ℚ)) + ((v kk none).toNNRat : ℚ)) -
        ((∑ i, ((-v kk (some i)).toNNRat : ℚ) * (R l i : ℚ)) + ((-v kk none).toNNRat : ℚ)) =
        v kk none + ∑ i, (R l i : ℚ) * v kk (some i) := by
      have e1 : (∑ i, ((v kk (some i)).toNNRat : ℚ) * (R l i : ℚ)) -
          (∑ i, ((-v kk (some i)).toNNRat : ℚ) * (R l i : ℚ)) = ∑ i, (R l i : ℚ) * v kk (some i) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← sub_mul, toNNRat_sub_neg]; ring
      have e2 := toNNRat_sub_neg (v kk none)
      linarith
    rw [e, h]
  have hsum : ∑ l, (z l : ℚ) * ((∑ i, ((v kk (some i)).toNNRat : ℚ) * (R l i : ℚ)) + ((v kk none).toNNRat : ℚ)) -
      ∑ l, (z l : ℚ) * ((∑ i, ((-v kk (some i)).toNNRat : ℚ) * (R l i : ℚ)) + ((-v kk none).toNNRat : ℚ)) =
      (z kk : ℚ) := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [← mul_sub, key]
    simp
  linarith

/-- A row against a unit vector is its entry. -/
theorem sum_mul_single {m : ℕ} (c : Fin m → ℕ) (j : Fin m) :
    ∑ i, (c i : ℚ) * (((Pi.single j 1 : Fin m → ℕ) i : ℕ) : ℚ) = (c j : ℚ) := by
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [hb]
  · simp

/-- A vector of a linearly independent set is outside the span of the rest. -/
theorem notMem_span_diff_singleton {V : Type*} [AddCommGroup V] [Module ℚ V] {b : Set V} {a : V}
    (hb : LinearIndepOn ℚ id b) (ha : a ∈ b) : a ∉ Submodule.span ℚ (b \ {a}) := by
  have hb' : LinearIndepOn ℚ id (b \ {a}) := hb.mono Set.sdiff_subset
  rw [hb'.notMem_span_iff_id]
  refine ⟨?_, fun h => h.2 rfl⟩
  rwa [Set.insert_sdiff_singleton, Set.insert_eq_of_mem ha]

/-- Rank and nullity, on a basis of rows. Rows of a part `I` (`pi > 0`) and of a part `J` (`rho > 0`) that span
`ℚ^m` contain a basis of `ℚ^m` that extends a basis of the span of the rows of `I` (`exists_linearIndependent`,
`exists_linearIndepOn_id_extension`); when the vectors on which the rows of `I` vanish lie in the directions of
`r = d + 1` points, that span has dimension at least `m - d` (`LinearMap.finrank_range_add_finrank_ker`), so at
most `d` rows of the basis lie in `J`. The basis is an invertible matrix; its inverse is split into its
positive part and its deficit. -/
theorem fact_basis_core :
    ∀ (m k r d : ℕ) (P N : Fin k → Fin m → ℕ) (pi rho : Fin k → NNRat) (W : Fin r → Fin m → ℕ), (r = d + (1 : ℕ)) → (∀ (j : Fin m), ∃ yP yM : Fin k → NNRat, (∀ (iota : Fin k), ((pi iota : ℚ) + (rho iota : ℚ) = (0 : ℚ)) → ((yP iota : ℚ) + (yM iota : ℚ) = (0 : ℚ))) ∧ (∀ x : Fin m → ℕ, (x j : ℚ) + (∑ iota : Fin k, (yP iota : ℚ) * ((∑ i : Fin m, N iota i * x i) : ℚ)) + (∑ iota : Fin k, (yM iota : ℚ) * ((∑ i : Fin m, P iota i * x i) : ℚ)) = (∑ iota : Fin k, (yP iota : ℚ) * ((∑ i : Fin m, P iota i * x i) : ℚ)) + (∑ iota : Fin k, (yM iota : ℚ) * ((∑ i : Fin m, N iota i * x i) : ℚ)))) → (∀ vP vM : Fin m → NNRat, (∀ (iota : Fin k), ((0 : ℚ) < (pi iota : ℚ)) → ((∑ i : Fin m, (P iota i : ℚ) * (vP i : ℚ)) + (∑ i : Fin m, (N iota i : ℚ) * (vM i : ℚ)) = (∑ i : Fin m, (N iota i : ℚ) * (vP i : ℚ)) + (∑ i : Fin m, (P iota i : ℚ) * (vM i : ℚ)))) → (∃ zP zM : Fin r → NNRat, ((∑ l : Fin r, (zP l : ℚ)) = (∑ l : Fin r, (zM l : ℚ))) ∧ (∀ (i : Fin m), (vP i : ℚ) + (∑ l : Fin r, (zM l : ℚ) * (W l i : ℚ)) = (vM i : ℚ) + (∑ l : Fin r, (zP l : ℚ) * (W l i : ℚ))))) → ∃ zeta : Fin m → Fin k → ℕ, ∃ h : Fin m → ℕ, ∃ nuP nuM : Fin m → Fin m → NNRat, (∀ (alpha : Fin m), (∑ iota : Fin k, zeta alpha iota) = (1 : ℕ)) ∧ (∀ (alpha : Fin m), h alpha ≤ (1 : ℕ)) ∧ (∀ (alpha : Fin m), ∀ (iota : Fin k), (((0 : ℕ) < zeta alpha iota) ∧ (h alpha = (0 : ℕ))) → ((0 : ℚ) < (pi iota : ℚ))) ∧ (∀ (alpha : Fin m), ∀ (iota : Fin k), (((0 : ℕ) < zeta alpha iota) ∧ (h alpha = (1 : ℕ))) → ((0 : ℚ) < (rho iota : ℚ))) ∧ ((∑ alpha : Fin m, h alpha) ≤ d) ∧ (∀ (i : Fin m), ∀ x : Fin m → ℕ, (x i : ℚ) + (∑ alpha : Fin m, ((nuP i alpha : ℚ) * ((∑ iota : Fin k, zeta alpha iota * (∑ j : Fin m, N iota j * x j)) : ℚ) + (nuM i alpha : ℚ) * ((∑ iota : Fin k, zeta alpha iota * (∑ j : Fin m, P iota j * x j)) : ℚ))) = (∑ alpha : Fin m, ((nuP i alpha : ℚ) * ((∑ iota : Fin k, zeta alpha iota * (∑ j : Fin m, P iota j * x j)) : ℚ) + (nuM i alpha : ℚ) * ((∑ iota : Fin k, zeta alpha iota * (∑ j : Fin m, N iota j * x j)) : ℚ)))) := by
  intro m k r d P N pi rho W hr hspan hker
  classical
  subst hr
  -- the rows over the rationals, the two parts, and their images
  let A : Fin k → (Fin m → ℚ) := fun ι i => (P ι i : ℚ) - (N ι i : ℚ)
  let I : Set (Fin k) := {ι | 0 < (pi ι : ℚ)}
  let J : Set (Fin k) := {ι | 0 < (rho ι : ℚ)}
  let s : Set (Fin m → ℚ) := A '' I
  let t : Set (Fin m → ℚ) := A '' (I ∪ J)
  -- (1) the rows of `I ∪ J` span `ℚ^m`
  have htop : Submodule.span ℚ t = ⊤ := by
    have hmem : ∀ j : Fin m, (Pi.single j 1 : Fin m → ℚ) ∈ Submodule.span ℚ t := by
      intro j
      obtain ⟨yP, yM, hsupp, hx⟩ := hspan j
      have hvec : (Pi.single j 1 : Fin m → ℚ) = ∑ ι, ((yP ι : ℚ) - (yM ι : ℚ)) • A ι := by
        funext j'
        have h := hx (Pi.single j' 1)
        simp only [sum_mul_single] at h
        have hxj : (((Pi.single j' 1 : Fin m → ℕ) j : ℕ) : ℚ) = (Pi.single j 1 : Fin m → ℚ) j' := by
          by_cases hjj : j = j'
          · subst hjj; simp
          · simp [hjj, Ne.symm hjj]
        rw [hxj] at h
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, A]
        have e : ∑ ι, ((yP ι : ℚ) - (yM ι : ℚ)) * ((P ι j' : ℚ) - (N ι j' : ℚ)) =
            ∑ ι, (yP ι : ℚ) * (P ι j' : ℚ) + ∑ ι, (yM ι : ℚ) * (N ι j' : ℚ) -
              (∑ ι, (yP ι : ℚ) * (N ι j' : ℚ) + ∑ ι, (yM ι : ℚ) * (P ι j' : ℚ)) := by
          simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun _ _ => by ring)
        rw [e]; linarith
      rw [hvec]
      refine Submodule.sum_mem _ (fun ι _ => ?_)
      by_cases hι : ι ∈ I ∪ J
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ι, hι, rfl⟩)
      · have hpi : (pi ι : ℚ) = 0 := by
          have := (pi ι).coe_nonneg
          have hn : ¬ (0 < (pi ι : ℚ)) := fun h' => hι (Or.inl h')
          linarith [not_lt.mp hn]
        have hrho : (rho ι : ℚ) = 0 := by
          have := (rho ι).coe_nonneg
          have hn : ¬ (0 < (rho ι : ℚ)) := fun h' => hι (Or.inr h')
          linarith [not_lt.mp hn]
        have hy := hsupp ι (by rw [hpi, hrho]; norm_num)
        have h1 := (yP ι).coe_nonneg
        have h2 := (yM ι).coe_nonneg
        have hP : (yP ι : ℚ) = 0 := by linarith
        have hM : (yM ι : ℚ) = 0 := by linarith
        rw [hP, hM, sub_zero, zero_smul]
        exact Submodule.zero_mem _
    refine eq_top_iff.2 ?_
    rw [← (Pi.basisFun ℚ (Fin m)).span_eq]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    simpa [Pi.basisFun_apply] using hmem j
  -- (2) the vectors on which the rows of `I` vanish lie in the directions of the points `W`
  let Bmask : Matrix (Fin k) (Fin m) ℚ := fun ι i => if 0 < (pi ι : ℚ) then A ι i else 0
  let f := Bmask.mulVecLin
  let g' : Fin d → (Fin m → ℚ) := fun l i => (W l.succ i : ℚ) - (W 0 i : ℚ)
  have hkerle : LinearMap.ker f ≤ Submodule.span ℚ (Set.range g') := by
    intro v hv
    have hv' : ∀ ι, 0 < (pi ι : ℚ) → ∑ i, A ι i * v i = 0 := by
      intro ι hι
      have h0 : (Bmask *ᵥ v) ι = 0 := congrFun (LinearMap.mem_ker.mp hv) ι
      simp only [Matrix.mulVec, dotProduct, Bmask, ite_eq_left hι] at h0
      exact h0
    obtain ⟨zP, zM, hz, hzv⟩ := hker (fun i => (v i).toNNRat) (fun i => (-v i).toNNRat) (by
      intro ι hι
      have h0 := hv' ι hι
      have e : ∑ i, A ι i * v i = (∑ i, (P ι i : ℚ) * ((v i).toNNRat : ℚ) + ∑ i, (N ι i : ℚ) * ((-v i).toNNRat : ℚ)) -
          (∑ i, (N ι i : ℚ) * ((v i).toNNRat : ℚ) + ∑ i, (P ι i : ℚ) * ((-v i).toNNRat : ℚ)) := by
        simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        have := toNNRat_sub_neg (v i)
        generalize ((v i).toNNRat : ℚ) = a at this ⊢
        generalize ((-v i).toNNRat : ℚ) = b at this ⊢
        simp only [A]
        rw [← this]; ring
      linarith)
    -- `v = Σ z_l W_l` with `Σ z_l = 0`
    let z : Fin (d + 1) → ℚ := fun l => (zP l : ℚ) - (zM l : ℚ)
    have hzsum : ∑ l, z l = 0 := by simp only [z, Finset.sum_sub_distrib]; linarith
    have hvz : v = ∑ l, z l • (fun i => (W l i : ℚ)) := by
      funext i
      have h1 := hzv i
      have h2 := toNNRat_sub_neg (v i)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, z]
      have e : ∑ l, ((zP l : ℚ) - (zM l : ℚ)) * (W l i : ℚ) =
          ∑ l, (zP l : ℚ) * (W l i : ℚ) - ∑ l, (zM l : ℚ) * (W l i : ℚ) := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [e]; linarith
    have hvg : v = ∑ l : Fin d, z l.succ • g' l := by
      rw [hvz]
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, g']
      rw [Fin.sum_univ_succ]
      have e0 : z 0 = -∑ l : Fin d, z l.succ := by
        have := hzsum; rw [Fin.sum_univ_succ] at this; linarith
      rw [e0]
      have e1 : ∑ l : Fin d, z l.succ * ((W l.succ i : ℚ) - (W 0 i : ℚ)) =
          ∑ l : Fin d, z l.succ * (W l.succ i : ℚ) - (∑ l : Fin d, z l.succ) * (W 0 i : ℚ) := by
        rw [Finset.sum_mul, ← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun _ _ => by ring)
      rw [e1]; ring
    rw [hvg]
    exact Submodule.sum_mem _ (fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩))
  have hkerdim : Module.finrank ℚ (LinearMap.ker f) ≤ d := by
    calc Module.finrank ℚ (LinearMap.ker f) ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range g')) :=
          Submodule.finrank_mono hkerle
      _ ≤ Fintype.card (Fin d) := finrank_range_le_card g'
      _ = d := Fintype.card_fin d
  -- (3) rank and nullity: the rows of `I` span a space of dimension at least `m - d`
  have hspan_s : Submodule.span ℚ (Set.range Bmask.row) = Submodule.span ℚ s := by
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨ι, rfl⟩
      by_cases hι : 0 < (pi ι : ℚ)
      · have : Bmask.row ι = A ι := by funext i; exact ite_eq_left hι
        rw [this]; exact Submodule.subset_span ⟨ι, hι, rfl⟩
      · have : Bmask.row ι = 0 := by funext i; exact ite_eq_right hι
        rw [this]; exact Submodule.zero_mem _
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨ι, hι, rfl⟩
      have : Bmask.row ι = A ι := by funext i; exact ite_eq_left (show 0 < (pi ι : ℚ) from hι)
      rw [← this]; exact Submodule.subset_span ⟨ι, rfl⟩
  have hrn : Module.finrank ℚ (Submodule.span ℚ s) + Module.finrank ℚ (LinearMap.ker f) = m := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [Module.finrank_fin_fun] at this
    have hr2 : Module.finrank ℚ (LinearMap.range f) = Module.finrank ℚ (Submodule.span ℚ s) := by
      rw [← hspan_s, ← Matrix.rank_eq_finrank_span_row]; rfl
    rw [← hr2]; exact this
  -- (4) a basis of the rows of `I`, extended by rows of `J` to a basis of `ℚ^m`
  obtain ⟨b0, hb0s, hb0span, hb0ind⟩ := exists_linearIndependent ℚ s
  have hb0 : LinearIndepOn ℚ id b0 := hb0ind
  obtain ⟨b, hbt, hb0b, htb, hbind⟩ :=
    exists_linearIndepOn_id_extension hb0 (hb0s.trans (Set.image_mono Set.subset_union_left))
  have hbtop : ⊤ ≤ Submodule.span ℚ (Set.range (fun x : b => (x : Fin m → ℚ))) := by
    rw [Subtype.range_coe, ← htop]
    exact Submodule.span_le.2 htb
  let bb : Basis b ℚ (Fin m → ℚ) := Basis.mk hbind hbtop
  have : Finite b := Module.Finite.finite_basis bb
  have : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = m := by
    rw [← Module.finrank_eq_card_basis bb, Module.finrank_fin_fun]
  have : Fintype b0 := ((Set.toFinite b).subset hb0b).fintype
  have hb0card : Module.finrank ℚ (Submodule.span ℚ s) = b0.toFinset.card := by
    rw [← hb0span, finrank_span_set_eq_card hb0]
  let e : Fin m ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  let u : Fin m → (Fin m → ℚ) := fun α => (e α : Fin m → ℚ)
  -- (5) the row of each member of the basis, in `I` for the members of `b0` and in `J` for the others
  have hsel : ∀ α, ∃ ι, A ι = u α ∧ (u α ∈ b0 → ι ∈ I) ∧ (u α ∉ b0 → ι ∈ J) := by
    intro α
    by_cases hα : u α ∈ b0
    · obtain ⟨ι, hι, he⟩ := hb0s hα
      exact ⟨ι, he, fun _ => hι, fun h' => absurd hα h'⟩
    · obtain ⟨ι, hι, he⟩ := hbt (e α).2
      refine ⟨ι, he, fun h' => absurd h' hα, fun _ => ?_⟩
      rcases hι with hI | hJ
      · exfalso
        have hin : u α ∈ Submodule.span ℚ b0 := by
          rw [hb0span]; exact Submodule.subset_span ⟨ι, hI, he⟩
        have hsub : b0 ⊆ b \ {u α} := fun x hx => ⟨hb0b hx, fun hx' => hα (hx' ▸ hx)⟩
        exact notMem_span_diff_singleton hbind (e α).2 (Submodule.span_mono hsub hin)
      · exact hJ
  choose ιf hιf using hsel
  -- (6) the basis as an invertible matrix
  let Bm : Matrix (Fin m) (Fin m) ℚ := fun α i => u α i
  have hli : LinearIndependent ℚ Bm.row := by
    have := hbind.comp e e.injective
    exact this
  have hU : IsUnit Bm := Matrix.linearIndependent_row_iff_isUnit.mp hli
  have hdet : IsUnit Bm.det := (Matrix.isUnit_iff_isUnit_det Bm).mp hU
  have hinv : Bm⁻¹ * Bm = 1 := Matrix.nonsing_inv_mul Bm hdet
  let ν := Bm⁻¹
  refine ⟨fun α ι => if ι = ιf α then 1 else 0, fun α => if u α ∈ b0 then 0 else 1,
    fun i α => (ν i α).toNNRat, fun i α => (-ν i α).toNNRat, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α; simp
  · intro α; show (if u α ∈ b0 then 0 else 1) ≤ 1; split_ifs <;> omega
  · intro α ι ⟨hz, hh⟩
    have hιe : ι = ιf α := by by_contra hne; simp [hne] at hz
    have hb : u α ∈ b0 := by by_contra hne; simp [hne] at hh
    subst hιe; exact (hιf α).2.1 hb
  · intro α ι ⟨hz, hh⟩
    have hιe : ι = ιf α := by by_contra hne; simp [hne] at hz
    have hb : u α ∉ b0 := by intro hne; simp [hne] at hh
    subst hιe; exact (hιf α).2.2 hb
  · -- at most `d` members of the basis lie outside `b0`
    have hsplit := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun α : Fin m => u α ∈ b0)
    have hin : (Finset.univ.filter (fun α : Fin m => u α ∈ b0)).card = b0.toFinset.card := by
      refine Finset.card_bij (fun α _ => u α) ?_ ?_ ?_
      · intro α hα; simpa using hα
      · intro α₁ _ α₂ _ he
        exact e.injective (Subtype.ext he)
      · intro x hx
        have hx' : x ∈ b0 := by simpa using hx
        refine ⟨e.symm ⟨x, hb0b hx'⟩, ?_, ?_⟩
        · simp [u, hx']
        · simp [u]
    have hsum : (∑ α : Fin m, (if u α ∈ b0 then 0 else 1 : ℕ)) =
        (Finset.univ.filter (fun α : Fin m => ¬ u α ∈ b0)).card := by
      rw [Finset.card_filter]
      exact Finset.sum_congr rfl (fun α _ => by split_ifs <;> rfl)
    rw [hsum]
    simp only [Finset.card_univ, Fintype.card_fin] at hsplit
    omega
  · intro i x
    -- the value of a member of the basis at `x`
    have hrow : ∀ (c : Fin k → ℕ) (α : Fin m),
        ∑ ι, (((if ι = ιf α then 1 else 0 : ℕ)) : ℚ) * (c ι : ℚ) = (c (ιf α) : ℚ) := by
      intro c α
      rw [Finset.sum_eq_single (ιf α)]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    simp only [hrow]
    have hx' : ν *ᵥ (Bm *ᵥ (fun j => (x j : ℚ))) = fun j => (x j : ℚ) := by
      rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
    have hxi := congrFun hx' i
    simp only [Matrix.mulVec, dotProduct] at hxi
    have hB : ∀ α, ∑ j, Bm α j * (x j : ℚ) = ((∑ j, P (ιf α) j * x j : ℕ) : ℚ) - ((∑ j, N (ιf α) j * x j : ℕ) : ℚ) := by
      intro α
      push_cast
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have := congrFun (hιf α).1 j
      simp only [Bm, ← this, A]; ring
    simp only [hB] at hxi
    have e : ∑ α, (((ν i α).toNNRat : ℚ) * ((∑ j, P (ιf α) j * x j : ℕ) : ℚ) +
          ((-ν i α).toNNRat : ℚ) * ((∑ j, N (ιf α) j * x j : ℕ) : ℚ)) -
        ∑ α, (((ν i α).toNNRat : ℚ) * ((∑ j, N (ιf α) j * x j : ℕ) : ℚ) +
          ((-ν i α).toNNRat : ℚ) * ((∑ j, P (ιf α) j * x j : ℕ) : ℚ)) =
        ∑ α, ν i α * (((∑ j, P (ιf α) j * x j : ℕ) : ℚ) - ((∑ j, N (ιf α) j * x j : ℕ) : ℚ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun α _ => ?_)
      have := toNNRat_sub_neg (ν i α)
      generalize ((ν i α).toNNRat : ℚ) = a at this ⊢
      generalize ((-ν i α).toNNRat : ℚ) = b at this ⊢
      rw [← this]; ring
    linarith

end Qpp.Cite
