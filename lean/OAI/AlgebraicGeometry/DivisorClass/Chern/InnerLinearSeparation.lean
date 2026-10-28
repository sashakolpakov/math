import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Inner Linear Separation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.InnerLinearSeparation

section

/-! Inner products against an injective linear image separate the original vectors. -/

theorem inner_linear_separates_left {A H : Type*} [AddCommGroup A] [Module ℂ A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (I : A →ₗ[ℂ] H) (hI : Function.Injective I) (a b : A)
    (hab : ∀ c : A, inner ℂ (I a) (I c) = inner ℂ (I b) (I c)) : a = b := by
  apply hI
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [inner_sub_left]
  apply sub_eq_zero.mpr
  simpa only [map_sub] using hab (a - b)

end

/-! A linear differential kills the remaining summand when it kills the sum and the first summand. -/

theorem linear_right_summand_zero {K A B : Type*} [Semiring K]
    [AddCommMonoid A] [Module K A] [AddCommMonoid B] [Module K B]
    (D : A →ₗ[K] B) (x y z : A) (h : x = y + z) (hy : D y = 0) (hx : D x = 0) : D z = 0 :=
  ((congrArg D h).trans ((map_add D y z).trans
    ((congrArg (fun v => v + D z) hy).trans (zero_add _)))).symm.trans hx

end OAI.AlgebraicGeometry.DivisorClass.Chern.InnerLinearSeparation
