set_option autoImplicit true

section Mathlib.Init.ZeroOne

class One (α : Type) where
  one : α

instance One.toOfNat1 {α} [One α] : OfNat α (nat_lit 1) where
  ofNat := ‹One α›.1

end Mathlib.Init.ZeroOne

section Mathlib.Algebra.Group.Defs

class MulOneClass (M : Type) extends One M, Mul M where
  one_mul : ∀ a : M, 1 * a = a

export MulOneClass (one_mul)

end Mathlib.Algebra.Group.Defs

section Mathlib.Algebra.Ring.Defs

class Distrib (R : Type) extends Mul R, Add R where
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

class RightDistribClass (R : Type) [Mul R] [Add R] : Prop where
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance Distrib.rightDistribClass (R : Type) [Distrib R] : RightDistribClass R :=
  ⟨Distrib.right_distrib⟩

theorem add_mul [Mul R] [Add R] [RightDistribClass R] (a b c : R) :
    (a + b) * c = a * c + b * c :=
  RightDistribClass.right_distrib a b c

theorem add_one_mul [Add α] [MulOneClass α] [RightDistribClass α] (a b : α) :
    (a + 1) * b = a * b + b := by
  rw [add_mul, one_mul]; done

class Semiring (R : Type) extends Distrib R, MulOneClass R

end Mathlib.Algebra.Ring.Defs

section Mathlib.Data.Nat.Basic

instance : Semiring Nat where
  add := Nat.add
  mul := Nat.mul
  one := Nat.succ Nat.zero
  one_mul := sorry
  right_distrib := sorry

end Mathlib.Data.Nat.Basic

#synth MulOneClass Nat       -- works
#synth RightDistribClass Nat -- works

example {a b : Nat} : (a + 1) * b = a * b + b :=
  have := add_one_mul a b -- works
  by rw [add_one_mul]     -- should not produce: failed to synthesize instance: RightDistribClass ?m
