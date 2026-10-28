import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalIntegralCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntegralUnitaryMatrices

/-! # Principal Local Integrality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalLocalIntegrality.CM

noncomputable section

/-! ThetaCycle: derive a genuine principal depth whose rational matrices and
inverses lie in every native local integral special-unitary subgroup. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.IntegralTopology

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)

theorem exists_principal_local_integral_depth (B : HeckeCycles.GeometricSource.CM.BallDatum K) :
    ∃ D : ℕ, 0 < D ∧ ∀ N : ℕ, D ∣ N →
      ∀ (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g)
        (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (maximalRealSubfield K))),
        RepresentationTheory.Theta.Adelic.RationalSU.rationalLocalSU (maximalRealSubfield K)
          (CMGlobalFrames.CM.cmHermitianUnit K δ hδ B.b B.conjugate_b
            (fun hb => (ne_of_lt B.negative) (by simp [hb]))) (.inr v)
          (RationalBallUnitary.CM.rationalBallSU K δ hδ hδ0 B N g hg) ∈
          RepresentationTheory.Theta.Adelic.IntegralTopology.localSUIntegral (maximalRealSubfield K)
            (CMGlobalFrames.CM.cmHermitianUnit K δ hδ B.b B.conjugate_b
              (fun hb => (ne_of_lt B.negative) (by simp [hb]))).val (.inr v) := by
  obtain ⟨D, hD, hcoeff⟩ := PrincipalIntegralCoordinates.CM.exists_principal_integral_coordinate_depth K δ hδ hδ0 B
  refine ⟨D, hD, ?_⟩
  intro N hN g hg v
  have hmatrix (u : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hu : B.principalLevel N u) (i j : Fin 3) :
      IsIntegral ℤ ((RationalBallUnitary.CM.rationalBallUnit K δ hδ hδ0 u).val i j).re ∧
        IsIntegral ℤ ((RationalBallUnitary.CM.rationalBallUnit K δ hδ hδ0 u).val i j).im := by
    apply IntegralUnitaryMatrices.CM.quadratic_matrix_entry_integral_of_difference
      (QuadraticModel.CM.cmQuadraticParameter K δ hδ) (RationalBallUnitary.CM.rationalBallUnit K δ hδ hδ0 u).val i j
    · rw [RationalBallCoordinates.CM.rational_ball_unit_difference]
      exact hcoeff N hN u hu i j 0
    · rw [RationalBallCoordinates.CM.rational_ball_unit_difference]
      exact hcoeff N hN u hu i j 1
  apply IntegralUnitaryMatrices.CM.local_rational_su_integral_of_coefficients
  · exact hmatrix g hg
  · intro i j
    change IsIntegral ℤ (((RationalBallUnitary.CM.rationalBallUnit K δ hδ hδ0 g)⁻¹).val i j).re ∧
      IsIntegral ℤ (((RationalBallUnitary.CM.rationalBallUnit K δ hδ hδ0 g)⁻¹).val i j).im
    rw [← RationalBallCoordinates.CM.rational_ball_unit_symm]
    exact hmatrix g.symm (PrincipalColumnBounds.CM.principal_level_symm K B N g hg) i j

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalLocalIntegrality.CM
