import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallActionMatrix
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverLocalM

/-! # Ball Line Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallLineAction.CM

noncomputable section

/-! ThetaCycle: the principal rational action is an actual smooth map of the
specified ball, with its literal projective-coordinate formula. -/

open scoped Classical _root_.Manifold ContDiff
open _root_.Matrix OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  (B : HeckeCycles.GeometricSource.CM.BallDatum K) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
  (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y)

include hg

theorem ball_action_image_negative (z : B.Domain) :
    let w := (BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val)
    Complex.normSq (w 0) + Complex.normSq (w 1) + (B.b : ℂ).re * Complex.normSq (w 2) < 0 := by
  dsimp only
  rw [BallActionMatrix.CM.ball_action_preserves_real_form K B g hg]
  change Complex.normSq (z.val 0) + Complex.normSq (z.val 1) +
    (B.b : ℂ).re * Complex.normSq 1 < 0
  rw [Complex.normSq_one, mul_one]
  have hz : Complex.normSq (z.val 0) + Complex.normSq (z.val 1) < -(B.b : ℂ).re := z.property
  linarith

theorem ball_action_denominator_ne_zero (z : B.Domain) :
    (BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2 ≠ 0 := by
  intro he
  have h := ball_action_image_negative K B g hg z
  dsimp only at h
  rw [he, Complex.normSq_zero, mul_zero, add_zero] at h
  exact (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)).not_gt h

theorem ball_line_action_mem (z : B.Domain) : HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val ∈ B.domain := by
  have h := ball_action_image_negative K B g hg z
  have hp := Complex.normSq_pos.mpr (ball_action_denominator_ne_zero K B g hg z)
  dsimp only at h
  change Complex.normSq (_ / _) + Complex.normSq (_ / _) < -(B.b : ℂ).re
  rw [Complex.normSq_div, Complex.normSq_div, ← add_div]
  change (Complex.normSq ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 0) +
    Complex.normSq ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 1)) /
    Complex.normSq ((BallActionMatrix.CM.ballActionMatrix K g).mulVec (HeckeCycles.GeometricSource.CM.BallDatum.lineVector z.val) 2) < -(B.b : ℂ).re
  rw [div_lt_iff₀ hp]
  nlinarith

def ballPrincipalAction : B.Domain → B.Domain :=
  fun z => ⟨HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val, ball_line_action_mem K B g hg z⟩

theorem ball_line_action_holomorphic :
    DifferentiableOn ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction (E := K) g) B.domain := by
  have hl : Differentiable ℂ HeckeCycles.GeometricSource.CM.BallDatum.lineVector := by
    intro z
    apply differentiableAt_pi.mpr
    intro i
    fin_cases i
    · change DifferentiableAt ℂ (fun x : HeckeCycles.GeometricSource.CM.BallChart => x 0) z
      fun_prop
    · change DifferentiableAt ℂ (fun x : HeckeCycles.GeometricSource.CM.BallChart => x 1) z
      fun_prop
    · change DifferentiableAt ℂ (fun _ : HeckeCycles.GeometricSource.CM.BallChart => (1 : ℂ)) z
      fun_prop
  have hw := (Matrix.toLin' (BallActionMatrix.CM.ballActionMatrix K g)).toContinuousLinearMap.differentiable.comp hl
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  apply differentiableAt_pi.mpr
  intro i
  have hn : DifferentiableAt ℂ (fun x => (BallActionMatrix.CM.ballActionMatrix K g).mulVec
      (HeckeCycles.GeometricSource.CM.BallDatum.lineVector x) i.castSucc) z :=
    (ContinuousLinearMap.proj i.castSucc : (Fin 3 → ℂ) →L[ℂ] ℂ).differentiable.comp hw z
  have hd : DifferentiableAt ℂ (fun x => (BallActionMatrix.CM.ballActionMatrix K g).mulVec
      (HeckeCycles.GeometricSource.CM.BallDatum.lineVector x) 2) z :=
    (ContinuousLinearMap.proj (2 : Fin 3) : (Fin 3 → ℂ) →L[ℂ] ℂ).differentiable.comp hw z
  simpa only [div_eq_mul_inv] using! hn.mul
    ((differentiableAt_inv (ball_action_denominator_ne_zero K B g hg ⟨z, hz⟩)).comp z hd)

theorem ball_principal_action_smooth :
    ContMDiff 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) ∞ (ballPrincipalAction K B g hg) := by
  have hs := (Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicDerivative.contDiffOn_infty_of_differentiableOn
    B.domain_isOpen (ball_line_action_holomorphic K B g hg)).restrict_scalars ℝ
  intro z
  apply (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff
    (U := B.domainOpen) _ Set.univ z).mp
  exact contMDiffAt_subtype_iff.mpr
    ((hs z.val z.property).contDiffAt (B.domain_isOpen.mem_nhds z.property)).contMDiffAt

omit hg in
theorem ball_principal_action_over_cover (N : ℕ) (hlevel : B.principalLevel N g)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : B.Domain → X.analyticSpace) (hπ : B.IsBallCover N X π) :
    π ∘ ballPrincipalAction K B g hlevel.1 = π := by
  funext z
  exact ((hπ.2.2.2.2.2 z (ballPrincipalAction K B g hlevel.1 z)).mpr
    ⟨g, hlevel, rfl⟩).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallLineAction.CM
