import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalLevel
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicFixedCovariance

/-! # Principal Geometric Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalGeometricLevel.CM

noncomputable section

/-! One actual principal level works for a fixed finite Schwartz family
and every admissible geometric period datum on the same rational tensor
space and global frame. The level is chosen before the geometric datum,
so it also works for an entire approximation family. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.GeometricGaussians OAI.RepresentationTheory.Theta.Adelic.GeometricGroup
open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallNatural.Factors

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K]
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)
  (B : HeckeCycles.GeometricSource.CM.BallDatum K) (m : ℕ) (hm : 0 < 3 * m)
  (W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield K)
    (QuadraticModel.CM.cmQuadraticParameter K δ hδ)))ˣ)
  (hW : W.val.conjTranspose = -W.val)
  (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 3 m
    (PrincipalFiniteLevel.CM.nativeBallHermitianUnit K δ hδ B) W)

theorem exists_principal_all_geometric_theta_level
    (Φ : Finset (RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (maximalRealSubfield K) (3 * m))) :
    ∃ D : ℕ, 0 < D ∧ ∀ N : ℕ, D ∣ N →
      PrincipalLevel.CM.PrincipalBallThetaInvariant K δ hδ hδ0 B m hm W hW P Φ N ∧
      ∀ (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g) (f : RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (maximalRealSubfield K) (3 * m)),
        f ∈ Φ →
        IntrinsicFixedCovariance.CM.NativeGeometricThetaCovariant P
          (RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU (maximalRealSubfield K) (PrincipalFiniteLevel.CM.nativeBallHermitianUnit K δ hδ B)
            (RationalBallUnitary.CM.rationalBallSU K δ hδ hδ0 B N g hg)) f := by
  have hlevel := PrincipalLevel.CM.exists_principal_ball_theta_level K δ hδ hδ0 B m hm W hW P Φ
  refine ⟨hlevel.choose, hlevel.choose_spec.1, ?_⟩
  intro N hN
  have hfix := hlevel.choose_spec.2 N hN
  refine ⟨hfix, ?_⟩
  intro g hg f hf
  exact IntrinsicFixedCovariance.CM.native_geometric_theta_covariant_of_invariant P
    (QuadraticModel.CM.cm_quadratic_parameter_ne_zero K δ hδ hδ0)
    (GlobalSplittingCharacters.CM.fieldGlobalSplittingCharacters (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ)
      (QuadraticModel.CM.cm_quadratic_parameter_ne_zero K δ hδ hδ0)
      (QuadraticModel.CM.cm_quadratic_parameter_not_isSquare K δ hδ hδ0) 3 m)
    (PrincipalLevel.CM.ballUnitarySplittings K δ hδ hδ0 B m hm W hW P)
    (GlobalSplittingCharacters.CM.field_global_splitting_characters_additive (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ)
      (QuadraticModel.CM.cm_quadratic_parameter_ne_zero K δ hδ hδ0)
      (QuadraticModel.CM.cm_quadratic_parameter_not_isSquare K δ hδ hδ0) 3 m)
    (RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU (maximalRealSubfield K) (PrincipalFiniteLevel.CM.nativeBallHermitianUnit K δ hδ B)
      (RationalBallUnitary.CM.rationalBallSU K δ hδ hδ0 B N g hg)) f (hfix g hg f hf)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalGeometricLevel.CM
