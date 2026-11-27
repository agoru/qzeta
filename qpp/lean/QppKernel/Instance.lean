module

public import QppKernel.Laws

/-!
# The tactic `qinst`: a result at given values

A reference `lem:y(k)[x := t]` is the statement of `lem:y(k)` at `x := t`. When the values are numerals, the instance
can differ from the goal by the evaluation of numerals only: `J ^ (1 : Count).toNat` is `J`, and
`x ^ (1 + 1 : Count).toNat` is `x ^ 2`. `qinst h` closes the goal with `h` as it is, or else after both are put in
that normal form (`toNat` of numerals, sums and products of counts; powers by one).
-/

public section

namespace Qpp

theorem Count.toNat_one : Count.toNat 1 = 1 := rfl

theorem Count.toNat_numeral (n : Nat) : Count.toNat (OfNat.ofNat (n + 1)) = n + 1 := Count.toNat_ofNatSucc n

theorem Count.pow_one (a : Count) : a ^ 1 = a := Count.one_mul a

theorem Mass.pow_one (x : Mass) : x ^ 1 = x := Mass.one_mul x

/-- `qinst h`: the goal is `h`, up to the evaluation of numerals in `h` and in the goal. -/
macro "qinst " h:term : tactic => `(tactic| first
  | exact $h
  | simpa only [Qpp.Count.toNat_one, Qpp.Count.toNat_numeral, Qpp.Count.toNat_add, Qpp.Count.toNat_mul,
      Qpp.Count.pow_one, Qpp.Mass.pow_one] using $h)

end Qpp
