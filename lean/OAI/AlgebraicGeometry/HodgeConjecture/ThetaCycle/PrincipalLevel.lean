import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalFiniteLevel
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicUnitarySplitting

/-! # Principal Level -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalLevel.CM

noncomputable section

/-! ThetaCycle: the constructed native splitting fixes any prescribed finite
Schwartz family at an actual principal level of the original ball lattice.
The level works for every archimedean test, hence is independent of periods. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary OAI.RepresentationTheory.Theta.Adelic.RationalSU
open OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)
  (B : HeckeCycles.GeometricSource.CM.BallDatum K)

theorem native_ball_hermitian_unit_conjugate_transpose :
    (PrincipalFiniteLevel.CM.nativeBallHermitianUnit K δ hδ B).val.conjTranspose =
      (PrincipalFiniteLevel.CM.nativeBallHermitianUnit K δ hδ B).val :=
  DiagonalFrame.CM.diagonal_hermitian_conjugateTranspose _ _

variable (m : ℕ) (hm : 0 < 3 * m)
  (W : (Matrix (Fin m) (Fin m) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield K)
    (QuadraticModel.CM.cmQuadraticParameter K δ hδ)))ˣ)
  (hW : W.val.conjTranspose = -W.val)
  (P : RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 3 m
    (PrincipalFiniteLevel.CM.nativeBallHermitianUnit K δ hδ B) W)

def ballUnitarySplittings :
    RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 3 m
      (PrincipalFiniteLevel.CM.nativeBallHermitianUnit K δ hδ B) W (QuadraticModel.CM.cm_quadratic_parameter_ne_zero K δ hδ hδ0)
      (GlobalSplittingCharacters.CM.fieldGlobalSplittingCharacters (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ)
        (QuadraticModel.CM.cm_quadratic_parameter_ne_zero K δ hδ hδ0)
        (QuadraticModel.CM.cm_quadratic_parameter_not_isSquare K δ hδ hδ0) 3 m) P :=
  IntrinsicUnitarySplitting.CM.fieldUnitarySplittings (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ)
    (QuadraticModel.CM.cm_quadratic_parameter_ne_zero K δ hδ hδ0)
    (QuadraticModel.CM.cm_quadratic_parameter_not_isSquare K δ hδ hδ0) 3 m hm
    (PrincipalFiniteLevel.CM.nativeBallHermitianUnit K δ hδ B) W
    (native_ball_hermitian_unit_conjugate_transpose K δ hδ B) hW P

def PrincipalBallThetaInvariant
    (Φ : Finset (RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (maximalRealSubfield K) (3 * m))) (N : ℕ) : Prop :=
  ∀ (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K) (hg : B.principalLevel N g), ∀ f ∈ Φ,
    ∀ φ : RepresentationTheory.Theta.Adelic.ThetaEvaluation.ArchimedeanTests (maximalRealSubfield K) (3 * m),
      RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta (maximalRealSubfield K) (3 * m)
        (RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta.archimedeanAction (maximalRealSubfield K) (PrincipalFiniteLevel.CM.nativeBallHermitianUnit K δ hδ B) W
          (QuadraticModel.CM.cm_quadratic_parameter_ne_zero K δ hδ hδ0)
          (GlobalSplittingCharacters.CM.fieldGlobalSplittingCharacters (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ)
            (QuadraticModel.CM.cm_quadratic_parameter_ne_zero K δ hδ hδ0)
            (QuadraticModel.CM.cm_quadratic_parameter_not_isSquare K δ hδ hδ0) 3 m) P
          (ballUnitarySplittings K δ hδ hδ0 B m hm W hW P)
          (RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU (maximalRealSubfield K) (PrincipalFiniteLevel.CM.nativeBallHermitianUnit K δ hδ B)
            (RationalBallUnitary.CM.rationalBallSU K δ hδ hδ0 B N g hg)) φ) f =
        RepresentationTheory.Theta.Adelic.ThetaEvaluation.theta (maximalRealSubfield K) (3 * m) φ f

theorem exists_principal_ball_theta_level
    (Φ : Finset (RepresentationTheory.Theta.Adelic.FiniteSchwartz.finiteSchwartz (maximalRealSubfield K) (3 * m))) :
    ∃ D : ℕ, 0 < D ∧ ∀ N : ℕ, D ∣ N →
      PrincipalBallThetaInvariant K δ hδ hδ0 B m hm W hW P Φ N := by
  have hlevel := IntrinsicUnitarySplitting.CM.field_unitary_finite_theta_level (maximalRealSubfield K)
    (QuadraticModel.CM.cmQuadraticParameter K δ hδ) (QuadraticModel.CM.cm_quadratic_parameter_ne_zero K δ hδ hδ0)
    (QuadraticModel.CM.cm_quadratic_parameter_not_isSquare K δ hδ hδ0) 3 m hm
    (PrincipalFiniteLevel.CM.nativeBallHermitianUnit K δ hδ B) W
    (native_ball_hermitian_unit_conjugate_transpose K δ hδ B) hW P Φ ⊤
  let L := hlevel.choose
  have hfix := hlevel.choose_spec.2.2
  have hdepth := PrincipalFiniteLevel.CM.principal_finite_level_cofinal K δ hδ hδ0 B L
  refine ⟨hdepth.choose, hdepth.choose_spec.1, ?_⟩
  intro N hN g hg f hf φ
  exact hfix f hf (RationalBallUnitary.CM.rationalBallSU K δ hδ hδ0 B N g hg)
    (hdepth.choose_spec.2 N hN g hg) φ

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PrincipalLevel.CM
