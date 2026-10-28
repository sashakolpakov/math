import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RationalBallCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.QuadraticCoefficientMaps
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalUnitaryNeighborhoods

/-! # Local Column Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalColumnCoordinates.CM

noncomputable section

/-! ThetaCycle: the actual local matrix and inverse differences are the
two quadratic coefficients of the original rational column differences. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.RationalSU

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)

def ballColumnDifferences (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (s : Fin 2) (j : Fin 3) : HeckeCycles.GeometricSource.CM.Vec K :=
  if s = 0 then g (Pi.single j 1) - Pi.single j 1 else g.symm (Pi.single j 1) - Pi.single j 1

theorem local_quadratic_identity_entry (v : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places (maximalRealSubfield K)) (i j : Fin 3) :
    RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ) v
      ((QuadraticModel.CM.cmQuadraticEquiv K δ hδ hδ0).symm ((Pi.single j 1 : HeckeCycles.GeometricSource.CM.Vec K) i)) =
      (1 : Matrix (Fin 3) (Fin 3) (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.localQuadratic (maximalRealSubfield K)
        (QuadraticModel.CM.cmQuadraticParameter K δ hδ) v)) i j := by
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem local_ball_column_pair (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N : ℕ) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
    (hg : B.principalLevel N g) (v : RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Places (maximalRealSubfield K)) :
    let q := RepresentationTheory.Theta.Adelic.RationalSU.rationalLocalSU (maximalRealSubfield K)
      (CMGlobalFrames.CM.cmHermitianUnit K δ hδ B.b B.conjugate_b
        (fun hb => (ne_of_lt B.negative) (by simp [hb]))) v
      (RationalBallUnitary.CM.rationalBallSU K δ hδ hδ0 B N g hg)
    (q.val.val - 1, (q⁻¹).val.val - 1) =
      LocalUnitaryNeighborhoods.CM.quadraticMatrixPair (RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (maximalRealSubfield K) v (QuadraticModel.CM.cmQuadraticParameter K δ hδ))
        (fun p : Fin 2 × Fin 3 × Fin 3 × Fin 2 =>
          RepresentationTheory.Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar (maximalRealSubfield K) v
            (QuadraticCoefficientMaps.CM.cmQuadraticCoefficient K δ hδ hδ0 p.2.2.2
              (ballColumnDifferences K g p.1 p.2.2.1 p.2.1))) := by
  dsimp only
  apply Prod.ext
  · apply Matrix.ext
    intro i j
    dsimp only
    rw [Matrix.sub_apply, RationalBallCoordinates.CM.rational_ball_local_entry, ← local_quadratic_identity_entry K δ hδ hδ0 v i j,
      ← map_sub, ← map_sub]
    apply QuadraticAlgebra.ext <;> rfl
  · apply Matrix.ext
    intro i j
    dsimp only
    rw [Matrix.sub_apply, RationalBallCoordinates.CM.rational_ball_local_inverse_entry, ← local_quadratic_identity_entry K δ hδ hδ0 v i j,
      ← map_sub, ← map_sub]
    apply QuadraticAlgebra.ext <;> rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.LocalColumnCoordinates.CM
