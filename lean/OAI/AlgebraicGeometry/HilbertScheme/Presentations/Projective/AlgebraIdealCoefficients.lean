import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SectionCoefficientIdeal
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.Noetherian.Basic

/-! # Algebra Ideal Coefficients -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.AlgebraIdealCoefficients

noncomputable section

/-! Equations on an affine source whose coordinate algebra is a projective
module over the base have a coefficient ideal detecting all base changes. -/

open TensorProduct

universe u v w
variable (R : Type u) [CommRing R]
variable (B : Type v) [CommRing B] [Algebra R B] [Module.Projective R B]

def projectiveAlgebraIdealCoefficients (J : Ideal B) : Ideal R :=
  SectionCoefficientIdeal.projectiveSectionCoefficientIdeal (R := R) (fun x : J => (x : B))

theorem projectiveAlgebraIdealCoefficients_test (J : Ideal B)
    (A : Type w) [CommRing A] [Algebra R A] :
    projectiveAlgebraIdealCoefficients R B J ≤ RingHom.ker (algebraMap R A) ↔
      J.map (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B) = ⊥ := by
  rw [projectiveAlgebraIdealCoefficients, SectionCoefficientIdeal.projectiveSectionCoefficientIdeal_le_ker_iff,
    Ideal.map_eq_bot_iff_le_ker]
  constructor
  · intro h b hb
    exact h ⟨b, hb⟩
  · intro h b
    exact h b.property

omit [Module.Projective R B] in
theorem projectiveAlgebraIdealCoefficients_finite [IsNoetherianRing R] (J : Ideal B) :
    (projectiveAlgebraIdealCoefficients R B J).FG :=
  IsNoetherian.noetherian _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.AlgebraIdealCoefficients
