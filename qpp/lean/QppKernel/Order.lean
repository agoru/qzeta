module

public import QppKernel.Laws

/-!
# The order

`a < b` when `b` is `a` plus something (defined in `Base.lean`): for counts `∃ c, b = a + c`, for masses `∃ z, y = x + z`. It is positive
existential, so maps that keep `1`, `+` and `/` keep it. Irreflexivity is the strong form of `neq`, and trichotomy
needs `ind`. On masses `p / q < r / s` exactly when `p * s < r * q` (`Mass.mk_lt_mk`), which reduces the order of
masses to that of counts.
-/

@[expose] public section

namespace Qpp

namespace Count

theorem lt_irrefl (a : Count) : ¬ a < a := fun ⟨c, h⟩ => add_ne_left a c h.symm

theorem lt_trans {a b c : Count} : a < b → b < c → a < c
  | ⟨d, hd⟩, ⟨e, he⟩ => ⟨d + e, by rw [he, hd, add_assoc]⟩

theorem lt_add (a b : Count) : a < a + b := ⟨b, rfl⟩

theorem lt_succ (a : Count) : a < succ a := ⟨1, rfl⟩

theorem one_lt_succ (a : Count) : 1 < succ a := ⟨a, (one_add a).symm⟩

theorem one_le (a : Count) : 1 ≤ a := by
  cases a with
  | one => exact Or.inl rfl
  | succ a => exact Or.inr (one_lt_succ a)

theorem lt_asymm {a b : Count} (h : a < b) : ¬ b < a := fun h' => lt_irrefl a (lt_trans h h')

theorem trichotomy (a b : Count) : a < b ∨ a = b ∨ b < a := by
  induction a using ind generalizing b with
  | h1 =>
    cases b with
    | one => exact Or.inr (Or.inl rfl)
    | succ b => exact Or.inl (one_lt_succ b)
  | hs a ih =>
    rcases ih b with ⟨c, rfl⟩ | rfl | h
    · cases c with
      | one => exact Or.inr (Or.inl rfl)
      | succ c => exact Or.inl ⟨c, by rw [add_succ, succ_add]⟩
    · exact Or.inr (Or.inr (lt_succ a))
    · exact Or.inr (Or.inr (lt_trans h (lt_succ a)))

theorem le_of_not_lt {a b : Count} (h : ¬ b < a) : a ≤ b := by
  rcases trichotomy a b with h' | h' | h'
  · exact Or.inr h'
  · exact Or.inl h'
  · exact absurd h' h

theorem not_lt_of_le {a b : Count} : a ≤ b → ¬ b < a
  | Or.inl rfl => lt_irrefl a
  | Or.inr h => lt_asymm h

theorem lt_of_le_of_lt {a b c : Count} : a ≤ b → b < c → a < c
  | Or.inl rfl, h => h
  | Or.inr h1, h2 => lt_trans h1 h2

/-- `a < b` gives `a + 1 ≤ b`. -/
theorem succ_le_of_lt {a b : Count} : a < b → succ a ≤ b
  | ⟨c, h⟩ => by
    subst h
    cases c with
    | one => exact Or.inl rfl
    | succ c => exact Or.inr ⟨c, by rw [add_succ, succ_add]⟩

theorem add_lt_add_right {a b : Count} (c : Count) : a < b → a + c < b + c
  | ⟨d, h⟩ => ⟨d, by rw [h]; qeq⟩

theorem lt_of_add_lt_add_right {a b c : Count} (h : a + c < b + c) : a < b := by
  rcases trichotomy a b with h' | rfl | h'
  · exact h'
  · exact absurd h (lt_irrefl _)
  · exact absurd (add_lt_add_right c h') (lt_asymm h)

theorem mul_lt_mul_right {a b : Count} (c : Count) : a < b → a * c < b * c
  | ⟨d, h⟩ => ⟨d * c, by rw [h, add_mul]⟩

theorem lt_of_mul_lt_mul_right {a b c : Count} (h : a * c < b * c) : a < b := by
  rcases trichotomy a b with h' | rfl | h'
  · exact h'
  · exact absurd h (lt_irrefl _)
  · exact absurd (mul_lt_mul_right c h') (lt_asymm h)

theorem toNat_lt {a b : Count} : a < b ↔ a.toNat < b.toNat := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [toNat_add]; have := toNat_pos c; omega
  · intro h
    rcases trichotomy a b with h' | rfl | ⟨c, rfl⟩
    · exact h'
    · exact absurd h (Nat.lt_irrefl _)
    · rw [toNat_add] at h; omega

end Count

namespace Mass

theorem mk_lt_mk {p q r s : Count} : mk p q < mk r s ↔ p * s < r * q := by
  constructor
  · rintro ⟨z, hz⟩
    induction z using ind_mk with | h u v =>
    rw [add_mk, mk_eq_mk] at hz
    apply Count.lt_of_mul_lt_mul_right (c := q * v)
    refine ⟨u * q * s * q, ?_⟩
    calc r * q * (q * v) = r * (q * v) * q := by qeq
      _ = (p * v + u * q) * s * q := by rw [hz]
      _ = p * s * (q * v) + u * q * s * q := by qeq
  · rintro ⟨c, hc⟩
    refine ⟨mk c (q * s), ?_⟩
    rw [add_mk, mk_eq_mk]
    calc r * (q * (q * s)) = (r * q) * (q * s) := by qeq
      _ = (p * s + c) * (q * s) := by rw [hc]
      _ = (p * (q * s) + c * q) * s := by qeq

theorem lt_irrefl (x : Mass) : ¬ x < x := fun ⟨z, h⟩ => add_ne_left x z h.symm

theorem lt_trans {x y z : Mass} : x < y → y < z → x < z
  | ⟨a, ha⟩, ⟨b, hb⟩ => ⟨a + b, by rw [hb, ha, add_assoc]⟩

theorem lt_asymm {x y : Mass} (h : x < y) : ¬ y < x := fun h' => lt_irrefl x (lt_trans h h')

theorem trichotomy (x y : Mass) : x < y ∨ x = y ∨ y < x := by
  induction x using ind_mk with | h p q =>
  induction y using ind_mk with | h r s =>
  rcases Count.trichotomy (p * s) (r * q) with h | h | h
  · exact Or.inl (mk_lt_mk.mpr h)
  · exact Or.inr (Or.inl (mk_eq_mk.mpr h))
  · exact Or.inr (Or.inr (mk_lt_mk.mpr h))

theorem le_of_not_lt {x y : Mass} (h : ¬ y < x) : x ≤ y := by
  rcases trichotomy x y with h' | h' | h'
  · exact Or.inr h'
  · exact Or.inl h'
  · exact absurd h' h

theorem not_lt_of_le {x y : Mass} : x ≤ y → ¬ y < x
  | Or.inl rfl => lt_irrefl x
  | Or.inr h => lt_asymm h

theorem lt_of_le_of_lt {x y z : Mass} : x ≤ y → y < z → x < z
  | Or.inl rfl, h => h
  | Or.inr h1, h2 => lt_trans h1 h2

theorem lt_of_lt_of_le {x y z : Mass} : x < y → y ≤ z → x < z
  | h, Or.inl rfl => h
  | h1, Or.inr h2 => lt_trans h1 h2

theorem add_lt_add_right {x y : Mass} (z : Mass) : x < y → x + z < y + z
  | ⟨a, h⟩ => ⟨a, by rw [h]; qeq⟩

theorem lt_of_add_lt_add_right {x y z : Mass} (h : x + z < y + z) : x < y := by
  rcases trichotomy x y with h' | rfl | h'
  · exact h'
  · exact absurd h (lt_irrefl _)
  · exact absurd (add_lt_add_right z h') (lt_asymm h)

theorem mul_lt_mul_right {x y : Mass} (z : Mass) : x < y → x * z < y * z
  | ⟨a, h⟩ => ⟨a * z, by rw [h]; qeq⟩

theorem ofCount_lt {a b : Count} : ofCount a < ofCount b ↔ a < b := by
  show mk a 1 < mk b 1 ↔ _
  rw [mk_lt_mk, Count.mul_one, Count.mul_one]

end Mass

end Qpp
