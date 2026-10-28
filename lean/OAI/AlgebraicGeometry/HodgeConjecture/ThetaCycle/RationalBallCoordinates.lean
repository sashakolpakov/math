import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalBallUnitary
import OAI.RepresentationTheory.Theta.Adelic.RationalSU

/-! # Rational Ball Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalBallCoordinates.CM

noncomputable section

/-! ThetaCycle: matrix entries and inverses of the actual native rational
special-unitary realization, before passage to local completions. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.RationalSU

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)

theorem rational_ball_unit_entry (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (i j : Fin 3) :
    (RationalBallUnitary.CM.rationalBallUnit K δ hδ hδ0 g).val i j =
      (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm (g (Pi.single j 1) i) := by
  rw [RationalBallUnitary.CM.rational_ball_unit_val]
  rfl

theorem rational_ball_unit_difference (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (i j : Fin 3) :
    (RationalBallUnitary.CM.rationalBallUnit K δ hδ hδ0 g).val i j -
      (1 : Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ))) i j =
      (QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm (g (Pi.single j 1) i - (Pi.single j 1 : HeckeCycles.GeometricSource.CM.Vec K) i) := by
  rw [rational_ball_unit_entry, map_sub]
  congr 1
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem rational_ball_unit_symm (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) :
    RationalBallUnitary.CM.rationalBallUnit K δ hδ hδ0 g.symm = (RationalBallUnitary.CM.rationalBallUnit K δ hδ hδ0 g)⁻¹ := by
  change RationalBallUnitary.CM.rationalBallUnit K δ hδ hδ0 g⁻¹ = _
  unfold RationalBallUnitary.CM.rationalBallUnit
  rw [LinearMap.GeneralLinearGroup.ofLinearEquiv_inv, map_inv, map_inv]

theorem rational_ball_local_entry (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (hg : B.principalLevel N g) (v : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places (maximalRealSubfield K)) (i j : Fin 3) :
    (RepresentationTheory.Theta.Adelic.RationalSU.rationalLocalSU (maximalRealSubfield K)
      (CMGlobalFrames.CM.cmHermitianUnit K δ hδ B.b B.conjugate_b
        (fun hb => (ne_of_lt B.negative) (by simp [hb]))) v
      (RationalBallUnitary.CM.rationalBallSU K δ hδ hδ0 B N g hg)).val.val i j =
      RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ) v
        ((QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm (g (Pi.single j 1) i)) := by
  change RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal _ _ v ((RationalBallUnitary.CM.rationalBallUnit K δ hδ hδ0 g).val i j) = _
  rw [rational_ball_unit_entry]

theorem rational_ball_local_inverse_entry (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (hg : B.principalLevel N g) (v : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places (maximalRealSubfield K)) (i j : Fin 3) :
    ((RepresentationTheory.Theta.Adelic.RationalSU.rationalLocalSU (maximalRealSubfield K)
      (CMGlobalFrames.CM.cmHermitianUnit K δ hδ B.b B.conjugate_b
        (fun hb => (ne_of_lt B.negative) (by simp [hb]))) v
      (RationalBallUnitary.CM.rationalBallSU K δ hδ hδ0 B N g hg))⁻¹).val.val i j =
      RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ) v
        ((QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm (g.symm (Pi.single j 1) i)) := by
  change RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal _ _ v ((RationalBallUnitary.CM.rationalBallUnit K δ hδ hδ0 g)⁻¹.val i j) = _
  rw [← rational_ball_unit_symm, rational_ball_unit_entry]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalBallCoordinates.CM
