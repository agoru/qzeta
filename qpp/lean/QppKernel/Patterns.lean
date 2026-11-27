module

public import QppKernel.MinMax
public import QppKernel.Scale

/-!
# The two quantifier patterns

Comparability: `f ≍ g` when `c g ≤ f ≤ C g` at every level, with the constants `c`, `C` named first (`Within` names
them, `Asymp` says they exist). Uniformity in a parameter: the constants come before the parameter's quantifier
(`AsympUnif`). The order of the quantifiers is the content: `asympUnif_not` is a family comparable for each parameter
and not uniformly.
-/

@[expose] public section

namespace Qpp

variable {ι π : Type}

/-- `c g ≤ f ≤ C g` at every level. -/
def Within (c C : Mass) (f g : ι → Mass) : Prop := ∀ i, c * g i ≤ f i ∧ f i ≤ C * g i

/-- `f ≍ g`: some constants `c`, `C` bound `f` by `g` at every level. -/
def Asymp (f g : ι → Mass) : Prop := ∃ c C : Mass, Within c C f g

/-- `f p ≍ g p` with constants that do not depend on the parameter `p`. -/
def AsympUnif (f g : π → ι → Mass) : Prop := ∃ c C : Mass, ∀ p, Within c C (f p) (g p)

/-- `f = O(g)`: some constant `C` bounds `f` by `C g` at every level. -/
def BigO (f g : ι → Mass) : Prop := ∃ C : Mass, ∀ i, f i ≤ C * g i

namespace Mass

theorem mul_le_mul_right' {a b : Mass} (c : Mass) : a ≤ b → a * c ≤ b * c
  | Or.inl rfl => Or.inl rfl
  | Or.inr h => Or.inr (mul_lt_mul_right c h)

end Mass

theorem Within.refl (f : ι → Mass) : Within 1 1 f f := fun i => by
  rw [Mass.one_mul]; exact ⟨Or.inl rfl, Or.inl rfl⟩

theorem Within.trans {c C c' C' : Mass} {f g h : ι → Mass} (h1 : Within c C f g) (h2 : Within c' C' g h) :
    Within (c * c') (C * C') f h := fun i => by
  obtain ⟨a1, b1⟩ := h1 i
  obtain ⟨a2, b2⟩ := h2 i
  constructor
  · have := Mass.mul_le_mul_left c a2
    rw [← Mass.mul_assoc] at this
    exact Mass.le_trans this a1
  · have := Mass.mul_le_mul_left C b2
    rw [← Mass.mul_assoc] at this
    exact Mass.le_trans b1 this

theorem Within.symm {c C : Mass} {f g : ι → Mass} (h : Within c C f g) : Within (1 / C) (1 / c) g f := fun i => by
  obtain ⟨a, b⟩ := h i
  constructor
  · have := Mass.mul_le_mul_left (1 / C) b
    rwa [show 1 / C * (C * g i) = g i by qeq] at this
  · have := Mass.mul_le_mul_left (1 / c) a
    rwa [show 1 / c * (c * g i) = g i by qeq] at this

theorem Asymp.refl (f : ι → Mass) : Asymp f f := ⟨1, 1, Within.refl f⟩

theorem Asymp.symm {f g : ι → Mass} : Asymp f g → Asymp g f
  | ⟨_, _, h⟩ => ⟨_, _, h.symm⟩

theorem Asymp.trans {f g h : ι → Mass} : Asymp f g → Asymp g h → Asymp f h
  | ⟨_, _, h1⟩, ⟨_, _, h2⟩ => ⟨_, _, h1.trans h2⟩

theorem AsympUnif.asymp {f g : π → ι → Mass} : AsympUnif f g → ∀ p, Asymp (f p) (g p)
  | ⟨c, C, h⟩, p => ⟨c, C, h p⟩

theorem Asymp.bigO {f g : ι → Mass} : Asymp f g → BigO f g
  | ⟨_, C, h⟩ => ⟨C, fun i => (h i).2⟩

/-- The order of the quantifiers is the content: `n ≍ 1` for each count `n`, but not uniformly in `n`. -/
theorem asympUnif_not :
    (∀ n : Count, Asymp (fun _ : Unit => Mass.ofCount n) (fun _ => 1)) ∧
      ¬ AsympUnif (fun (n : Count) (_ : Unit) => Mass.ofCount n) (fun _ _ => 1) := by
  constructor
  · intro n
    refine ⟨Mass.ofCount n, Mass.ofCount n, fun _ => ?_⟩
    rw [Mass.mul_one]; exact ⟨Or.inl rfl, Or.inl rfl⟩
  · rintro ⟨c, C, h⟩
    obtain ⟨N, hN⟩ := Mass.arch 1 C
    rw [Mass.mul_one] at hN
    have := (h N ()).2
    rw [Mass.mul_one] at this
    exact Mass.not_lt_of_le this hN

end Qpp
