import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Finite.CoefficientTopology
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Coefficient Vector Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoefficientVectorCoordinates.TestTransport

noncomputable section

/-! Any specified rational basis of the original vector space extends
to continuous coordinates on the PEL finite coefficient vectors. -/

open scoped Classical TensorProduct

variable (E : Type) [Field E] [NumberField E]
  {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def coefficientVectorCoordinates (p : (I → E) ≃ₗ[ℚ] (J → ℚ)) :
    (I → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) ≃ₗ[AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles] (J → AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) :=
  (TensorProduct.piRight ℚ AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles (fun _ : I => E)).symm.trans
    ((LinearEquiv.baseChange ℚ AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles (I → E) (J → ℚ) p).trans
      (TensorProduct.piScalarRight ℚ AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles J))

theorem coefficientVectorLinearMap_continuous
    {W : Type*} [AddCommGroup W] [Module AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles W]
    [TopologicalSpace W] [IsTopologicalAddGroup W] [ContinuousSMul AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles W]
    (f : (I → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) →ₗ[AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles] W) : Continuous f := by
  have he (x : I → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) : f x = ∑ i, f (Pi.single i (x i)) := by
    rw [← map_sum, Finset.univ_sum_single]
  have hc (i : I) : Continuous (fun y : AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E => f (Pi.single i y)) :=
    AbelianModuli.ReferenceFamily.AdelicCoefficientTopology.finiteCoefficientLinearMap_continuous (f.comp (LinearMap.single AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles
      (fun _ : I => AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) i))
  exact (continuous_finsetSum _ (fun i _ => (hc i).comp (continuous_apply i))).congr
    (fun x => (he x).symm)

def coefficientVectorHomeomorph (p : (I → E) ≃ₗ[ℚ] (J → ℚ)) :
    (I → AbelianModuli.ReferenceFamily.AdelicData.FiniteCoefficients E) ≃ₜ (J → AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) where
  toEquiv := (coefficientVectorCoordinates E p).toEquiv
  continuous_toFun := coefficientVectorLinearMap_continuous E (coefficientVectorCoordinates E p).toLinearMap
  continuous_invFun := (coefficientVectorCoordinates E p).symm.toLinearMap.continuous_on_pi

theorem coefficientVectorCoordinates_rational (p : (I → E) ≃ₗ[ℚ] (J → ℚ)) (x : I → E) :
    coefficientVectorCoordinates E p (fun i => AbelianModuli.ReferenceFamily.AdelicData.finiteCoefficientEmbedding E (x i)) =
      fun j => algebraMap ℚ AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles (p x j) := by
  change TensorProduct.piScalarRight ℚ AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles J
    ((LinearEquiv.baseChange ℚ AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles (I → E) (J → ℚ) p)
      ((TensorProduct.piRight ℚ AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles (fun _ : I => E)).symm
        (fun i => (1 : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) ⊗ₜ[ℚ] x i))) = _
  rw [TensorProduct.piRight_symm_apply]
  funext j
  change (p x j) • (1 : AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles) = algebraMap ℚ AbelianModuli.ReferenceFamily.AdelicData.RationalFiniteAdeles (p x j)
  simp only [Algebra.smul_def, mul_one]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoefficientVectorCoordinates.TestTransport
