import OAI.RepresentationTheory.Theta.Geometric.SquareZero.LinearDetection

/-! # Subalgebra -/

namespace OAI.RepresentationTheory.Theta.Geometric.SquareZero.Subalgebra

noncomputable section

/-! The constants together with an injected square-zero complex vector
space form an actual split square-zero subalgebra of the ambient ring. -/

variable {M R : Type*} [AddCommGroup M] [Module ℂ M] [Module ℂᵐᵒᵖ M] [IsCentralScalar ℂ M]
    [CommRing R] [Algebra ℂ R]

def squareZeroSubalgebraMap (i : M →ₗ[ℂ] R) (hsq : ∀ x y, i x * i y = 0) :
    TrivSqZeroExt ℂ M →ₐ[ℂ] R :=
  TrivSqZeroExt.liftEquivOfComm ⟨i, hsq⟩

theorem squareZeroSubalgebraMap_apply (i : M →ₗ[ℂ] R) (hsq : ∀ x y, i x * i y = 0)
    (x : TrivSqZeroExt ℂ M) :
    squareZeroSubalgebraMap i hsq x = algebraMap ℂ R x.fst + i x.snd := rfl

theorem squareZeroSubalgebraMap_eq_zero [Nontrivial R]
    (i : M →ₗ[ℂ] R) (hi : Function.Injective i) (hsq : ∀ x y, i x * i y = 0)
    (x : TrivSqZeroExt ℂ M) (hx : squareZeroSubalgebraMap i hsq x = 0) : x = 0 := by
  have hsum : algebraMap ℂ R x.fst + i x.snd = 0 := hx
  have hc : algebraMap ℂ R x.fst = -i x.snd := eq_neg_of_add_eq_zero_left hsum
  have hc2 : algebraMap ℂ R (x.fst * x.fst) = 0 := by
    rw [map_mul, hc, neg_mul_neg, hsq]
  have hc0 : x.fst = 0 := mul_self_eq_zero.mp
    ((algebraMap ℂ R).injective (hc2.trans (map_zero (algebraMap ℂ R)).symm))
  have hm : i x.snd = 0 := by
    simpa only [hc0, map_zero, zero_add] using hsum
  exact TrivSqZeroExt.ext hc0 (hi (hm.trans (map_zero i).symm))

theorem squareZeroSubalgebraMap_injective [Nontrivial R]
    (i : M →ₗ[ℂ] R) (hi : Function.Injective i) (hsq : ∀ x y, i x * i y = 0) :
    Function.Injective (squareZeroSubalgebraMap i hsq) := by
  intro x y h
  apply sub_eq_zero.mp
  apply squareZeroSubalgebraMap_eq_zero i hi hsq
  rw [map_sub, h, sub_self]

end

end OAI.RepresentationTheory.Theta.Geometric.SquareZero.Subalgebra
