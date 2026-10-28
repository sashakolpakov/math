import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceOneCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceDescent

/-! # Source Ball Covariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceBallCovariance.CM

noncomputable section

/-! ThetaCycle: the source cotangent identity is the pullback identity for
the actual smooth manifold one-form on the ball. -/

open scoped Classical _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

theorem open_inclusion_mfderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : TopologicalSpace.Opens E) (x : U) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → E) x = ContinuousLinearMap.id ℝ E := by
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E x) x = _
  rw [mfderiv_chartAt_eq_tangentCoordChange (mem_chart_source E x)]
  apply ContinuousLinearMap.ext
  intro ξ
  exact tangentCoordChange_self (I := 𝓘(ℝ, E)) (x := x) (z := x)
    (v := ξ) (mem_extChartAt_source x)

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  (B : HeckeCycles.GeometricSource.CM.BallDatum K) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
  (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y)

theorem ball_principal_action_mfderiv (z : B.Domain) :
    mfderiv 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) (BallLineAction.CM.ballPrincipalAction K B g hg) z =
      (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val).restrictScalars ℝ := by
  have hu : ContMDiff 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) ∞
      (Subtype.val : B.Domain → HeckeCycles.GeometricSource.CM.BallChart) := contMDiff_subtype_val
  have hball := (BallLineAction.CM.ball_principal_action_smooth K B g hg).mdifferentiableAt (by simp) (x := z)
  have hf : DifferentiableAt ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val :=
    (BallLineAction.CM.ball_line_action_holomorphic K B g hg z.val z.property).differentiableAt
      (B.domain_isOpen.mem_nhds z.property)
  have hfr := hf.restrictScalars ℝ
  have he : (Subtype.val : B.Domain → HeckeCycles.GeometricSource.CM.BallChart) ∘ BallLineAction.CM.ballPrincipalAction K B g hg =
      HeckeCycles.GeometricSource.CM.BallDatum.lineAction g ∘ (Subtype.val : B.Domain → HeckeCycles.GeometricSource.CM.BallChart) := rfl
  have hleft := mfderiv_comp z (hu.mdifferentiableAt (by simp)) hball
  have hright := mfderiv_comp z hfr.mdifferentiableAt (hu.mdifferentiableAt (by simp))
  change mfderiv 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart)
    ((Subtype.val : B.Domain → HeckeCycles.GeometricSource.CM.BallChart) ∘ BallLineAction.CM.ballPrincipalAction K B g hg) z = _ at hleft
  rw [he, hright, open_inclusion_mfderiv, open_inclusion_mfderiv] at hleft
  have hder : fderiv ℝ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val =
      mfderiv 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) (BallLineAction.CM.ballPrincipalAction K B g hg) z := by
    simpa only [ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id, mfderiv_eq_fderiv] using! hleft
  exact hder.symm.trans (hf.hasFDerivAt.restrictScalars ℝ).fderiv

variable {B} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Gal(K/ℚ) → Bool} (L : HeckeCycles.GeometricSource.CM.LinePeriod K B places d)

theorem source_ball_pullback_of_cotangent (φ Ψ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places))
    (h : ∀ (z : B.Domain) (ξ : HeckeCycles.GeometricSource.CM.BallChart),
      HeckeCycles.GeometricSource.CM.thetaOneForm K L Ψ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)
          (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val ξ) = HeckeCycles.GeometricSource.CM.thetaOneForm K L φ z.val ξ) :
    (BallForms.CM.sourceBallOneForm K L Ψ).val.pullback (BallLineAction.CM.ballPrincipalAction K B g hg) =
      (BallForms.CM.sourceBallOneForm K L φ).val := by
  funext z
  apply ContinuousAlternatingMap.ext
  intro v
  have hv : v = fun _ : Fin 1 => v 0 := funext (fun i => congrArg v (Subsingleton.elim i 0))
  rw [hv]
  change (BallForms.CM.sourceBallOneForm K L Ψ).val (BallLineAction.CM.ballPrincipalAction K B g hg z)
    (fun _ : Fin 1 => mfderiv 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart)
      (BallLineAction.CM.ballPrincipalAction K B g hg) z (v 0)) = _
  calc
    _ = HeckeCycles.GeometricSource.CM.thetaOneForm K L Ψ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val)
        (mfderiv 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) (BallLineAction.CM.ballPrincipalAction K B g hg) z (v 0)) := by
      simpa only using! SourceDescent.CM.source_ball_one_apply K L Ψ (BallLineAction.CM.ballPrincipalAction K B g hg z)
        (mfderiv 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) (BallLineAction.CM.ballPrincipalAction K B g hg) z (v 0))
    _ = HeckeCycles.GeometricSource.CM.thetaOneForm K L φ z.val (v 0) := by
      rw [ball_principal_action_mfderiv]
      exact h z (v 0)
    _ = _ := by simpa only using! (SourceDescent.CM.source_ball_one_apply K L φ z (v 0)).symm

variable [IsGalois ℚ K]

theorem exists_source_ball_covariant_input (hdet : LinearMap.det g.toLinearMap = 1)
    (φ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) :
    ∃ Ψ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places),
      (BallForms.CM.sourceBallOneForm K L Ψ).val.pullback (BallLineAction.CM.ballPrincipalAction K B g hg) =
        (BallForms.CM.sourceBallOneForm K L φ).val := by
  obtain ⟨Ψ, hΨ⟩ := SourceOneCovariance.CM.exists_source_one_covariant_input K g hdet L hg φ
  exact ⟨Ψ, source_ball_pullback_of_cotangent K g hg L φ Ψ hΨ⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceBallCovariance.CM
