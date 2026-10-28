import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceBallCovariance
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.PureTopCoefficient

/-! # Ball Top Form Invariance -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallTopFormInvariance.CM

noncomputable section

/-! The literal top-degree coefficient transformation is the pullback
identity for actual smooth pure forms on the original ball manifold. -/

open scoped Classical _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

theorem open_tangent_equiv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : TopologicalSpace.Opens E) (z : U) (ξ : E) : Analysis.DifferentialForms.Manifold.OpenEquivalence.openTangentEquiv z ξ = ξ := by
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (chartAt E z) z ξ = ξ
  rw [mfderiv_chartAt_eq_tangentCoordChange (mem_chart_source E z)]
  exact tangentCoordChange_self (I := 𝓘(ℝ, E)) (x := z) (z := z) (v := ξ) (mem_extChartAt_source z)

theorem open_tangent_equiv_symm_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : TopologicalSpace.Opens E) (z : U) (ξ : E) : (Analysis.DifferentialForms.Manifold.OpenEquivalence.openTangentEquiv z).symm ξ = ξ := by
  have h := open_tangent_equiv_apply U z ((Analysis.DifferentialForms.Manifold.OpenEquivalence.openTangentEquiv z).symm ξ)
  exact h.symm.trans ((Analysis.DifferentialForms.Manifold.OpenEquivalence.openTangentEquiv z).apply_symm_apply ξ)

theorem open_raw_form_inChart {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : TopologicalSpace.Opens E) (n : ℕ) (form : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E U n)
    (e : OpenPartialHomeomorph U E) (he : e ∈ atlas E U) (z : U) :
    form.inChart e z.val = form z := by
  rw [← Analysis.DifferentialForms.Manifold.OpenEquivalence.openRawManifoldEquiv_symm_eq_inChart form e he z]
  apply ContinuousAlternatingMap.ext
  intro v
  change form z (fun i => (Analysis.DifferentialForms.Manifold.OpenEquivalence.openTangentEquiv z).symm (v i)) = form z v
  exact congrArg (form z) (funext (fun i => open_tangent_equiv_symm_apply U z (v i)))

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  (B : HeckeCycles.GeometricSource.CM.BallDatum K) (g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K)
  (hg : ∀ x y, HeckeCycles.GeometricSource.CM.hermitian K B.b (g x) (g y) = HeckeCycles.GeometricSource.CM.hermitian K B.b x y)

theorem ball_top_pullback_of_coefficient (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm HeckeCycles.GeometricSource.CM.BallChart B.Domain 2)
    (hp : Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree HeckeCycles.GeometricSource.CM.BallChart B.Domain 2 0 form.val) (f : HeckeCycles.GeometricSource.CM.BallChart → ℂ)
    (hf : ∀ (e : OpenPartialHomeomorph B.Domain HeckeCycles.GeometricSource.CM.BallChart), e ∈ atlas HeckeCycles.GeometricSource.CM.BallChart B.Domain →
      ∀ z ∈ B.domain, form.val.inChart e z (Pi.basisFun ℂ (Fin 2)) = f z)
    (hinv : ∀ z : B.Domain,
      f (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) * LinearMap.det (fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val).toLinearMap = f z.val) :
    form.val.pullback (BallLineAction.CM.ballPrincipalAction K B g hg) = form.val := by
  have hpoint (z : B.Domain) : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree HeckeCycles.GeometricSource.CM.BallChart 2 0 (form.val z) := by
    have h := hp (chartAt HeckeCycles.GeometricSource.CM.BallChart z) (chart_mem_atlas HeckeCycles.GeometricSource.CM.BallChart z) z.val
      (by simpa only [Analysis.DifferentialForms.Manifold.OpenEquivalence.open_chartAt_target] using! z.property)
    rw [open_raw_form_inChart B.domainOpen 2 form.val _ (chart_mem_atlas HeckeCycles.GeometricSource.CM.BallChart z) z] at h
    exact h
  have hvalue (z : B.Domain) : form.val z (Pi.basisFun ℂ (Fin 2)) = f z.val := by
    have h := hf (chartAt HeckeCycles.GeometricSource.CM.BallChart z) (chart_mem_atlas HeckeCycles.GeometricSource.CM.BallChart z) z.val z.property
    rw [open_raw_form_inChart B.domainOpen 2 form.val _ (chart_mem_atlas HeckeCycles.GeometricSource.CM.BallChart z) z] at h
    exact h
  funext z
  apply ContinuousAlternatingMap.ext
  intro u
  change Fin 2 → HeckeCycles.GeometricSource.CM.BallChart at u
  change form.val (BallLineAction.CM.ballPrincipalAction K B g hg z)
    (fun i => mfderiv 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) 𝓘(ℝ, HeckeCycles.GeometricSource.CM.BallChart) (BallLineAction.CM.ballPrincipalAction K B g hg) z (u i)) = form.val z u
  rw [SourceBallCovariance.CM.ball_principal_action_mfderiv]
  change form.val (BallLineAction.CM.ballPrincipalAction K B g hg z)
    (fun i => fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val (u i)) = form.val z u
  have hl := (Analysis.HodgeTheory.Pure.Constructions.PolarizedPairing.pure_eq_basis_det _ (hpoint (BallLineAction.CM.ballPrincipalAction K B g hg z)) (Pi.basisFun ℂ (Fin 2))
    (fun i => fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val (u i))).trans
      (congrArg (fun c : ℂ => c * (Pi.basisFun ℂ (Fin 2)).det
        (fun i => fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val (u i))) (hvalue (BallLineAction.CM.ballPrincipalAction K B g hg z)))
  have hr := (Analysis.HodgeTheory.Pure.Constructions.PolarizedPairing.pure_eq_basis_det _ (hpoint z) (Pi.basisFun ℂ (Fin 2)) u).trans
    (congrArg (fun c : ℂ => c * (Pi.basisFun ℂ (Fin 2)).det u) (hvalue z))
  refine hl.trans (Eq.trans ?_ hr.symm)
  change f (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g z.val) *
    (Pi.basisFun ℂ (Fin 2)).det ((fderiv ℂ (HeckeCycles.GeometricSource.CM.BallDatum.lineAction g) z.val).toLinearMap ∘ u) = _
  rw [Module.Basis.det_comp, ← mul_assoc, hinv z]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BallTopFormInvariance.CM
