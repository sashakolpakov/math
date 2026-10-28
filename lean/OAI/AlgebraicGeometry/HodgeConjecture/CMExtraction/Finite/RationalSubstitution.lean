import OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Rational Substitution -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.RationalSubstitution.TestTransport

noncomputable section

/-! Rational invertible substitutions act on actual finite Schwartz
functions by pullback and commute with diagonal rational evaluation. -/

open scoped Classical _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rationalPositionMatrix (e : (ι → ℚ) ≃ₗ[ℚ] (ι → ℚ)) : (Matrix ι ι ℚ)ˣ :=
  Units.map LinearMap.toMatrixAlgEquiv'.toMonoidHom
    (LinearMap.GeneralLinearGroup.ofLinearEquiv e)

def finitePositionMatrix (e : (ι → ℚ) ≃ₗ[ℚ] (ι → ℚ)) : (Matrix ι ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf)ˣ :=
  Matrix.GeneralLinearGroup.map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) (rationalPositionMatrix e)

omit [DecidableEq ι] in
theorem finite_mulVec_continuous (M : Matrix ι ι RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) : Continuous (M.mulVec) := by
  apply continuous_pi
  intro i
  change Continuous (fun x : ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf => ∑ j, M i j * x j)
  fun_prop

def finitePositionHomeomorph (e : (ι → ℚ) ≃ₗ[ℚ] (ι → ℚ)) :
    (ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) ≃ₜ (ι → RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) where
  toFun := (finitePositionMatrix e).val.mulVec
  invFun := (finitePositionMatrix e).inv.mulVec
  left_inv x := by
    rw [Matrix.mulVec_mulVec, (finitePositionMatrix e).inv_val, Matrix.one_mulVec]
  right_inv x := by
    rw [Matrix.mulVec_mulVec, (finitePositionMatrix e).val_inv, Matrix.one_mulVec]
  continuous_toFun := finite_mulVec_continuous _
  continuous_invFun := finite_mulVec_continuous _

theorem finitePositionHomeomorph_rational (e : (ι → ℚ) ≃ₗ[ℚ] (ι → ℚ)) (x : ι → ℚ) :
    finitePositionHomeomorph e (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x) = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (e x) := by
  change (LinearMap.toMatrix' e.toLinearMap).map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) *ᵥ
    RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (e x)
  have hm : (LinearMap.toMatrix' e.toLinearMap).map (algebraMap ℚ RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.AQf) *ᵥ
      RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x = RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (LinearMap.toMatrix' e.toLinearMap *ᵥ x) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal, Matrix.map_apply, map_sum, map_mul]
  rw [hm, LinearMap.toMatrix'_mulVec]
  rfl

def finiteRationalPullback (e : (ι → ℚ) ≃ₗ[ℚ] (ι → ℚ))
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι :=
  ⟨φ.val ∘ finitePositionHomeomorph e,
    (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mpr
      ⟨((RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mp φ.property).1.comp_continuous
          (finitePositionHomeomorph e).continuous,
        (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_hasCompactSupport φ).comp_homeomorph (finitePositionHomeomorph e)⟩⟩

theorem finiteRationalPullback_rational (e : (ι → ℚ) ≃ₗ[ℚ] (ι → ℚ))
    (φ : RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) (x : ι → ℚ) :
    (finiteRationalPullback e φ).val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x) = φ.val (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal (e x)) := by
  change φ.val (finitePositionHomeomorph e (RepresentationTheory.Theta.PoissonAutomorphyNormalizationData.finiteDiagonal x)) = _
  rw [finitePositionHomeomorph_rational]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.RationalSubstitution.TestTransport
