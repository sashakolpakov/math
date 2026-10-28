import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicRefinement
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverPullback
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Betti
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveNaturality
import OAI.AlgebraicTopology.Kunneth.ProjectiveCupPurity
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation

/-! # Refinement Forms -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RefinementForms.CM

noncomputable section

/-! Actual closed forms and their canonical Betti classes under a deeper
principal cover. Conjugation and the nonzero cup evaluation are preserved. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff
open OAI.AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions

variable {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}

def projectiveClosedPullback (f : X.toOver ⟶ Y.toOver) (n : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms Y.analyticModel Y.analyticSpace n →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms X.analyticModel X.analyticSpace n :=
  Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldClosedFormsPullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f) (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map f ∞) n

theorem projective_form_class_pullback (f : X.toOver ⟶ Y.toOver) (n : ℕ)
    (α : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms Y.analyticModel Y.analyticSpace n) :
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass Y n α) =
      AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass X n (projectiveClosedPullback f n α) := by
  have h := ConcreteCategory.congr_hom (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamBettiIso_naturality f n) (Y.deRhamClass n α)
  change _ = (X.deRhamBettiIso n).hom
    (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback f n (Y.deRhamClass n α)) at h
  exact h.trans (congrArg (X.deRhamBettiIso n).hom
    (Analysis.DifferentialForms.Manifold.ClosedPullback.manifoldDeRhamFormClass_pullback_apply (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f)
      (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.real_contMDiff_map f ∞) n α))

theorem projective_closed_pullback_conjugate (f : X.toOver ⟶ Y.toOver) (n : ℕ)
    (α : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms Y.analyticModel Y.analyticSpace n) :
    projectiveClosedPullback f n (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm α) =
      ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm (projectiveClosedPullback f n α) := by
  apply Subtype.ext
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  ext u
  rfl

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {N M : ℕ}
  {S : Cm.PrincipalBallSurface K B N} {T : Cm.PrincipalBallSurface K B M}

theorem refinement_ball_form_pullback (p : Cm.PrincipalRefinement K S T) (n : ℕ)
    (α : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms S.surface.variety.analyticModel S.surface.variety.analyticSpace n) :
    CoverPullback.CM.ballCoverPullback K B M T.surface.variety T.projection T.isBallCover n
      (projectiveClosedPullback p.map n α).val =
        CoverPullback.CM.ballCoverPullback K B N S.surface.variety S.projection S.isBallCover n α.val := by
  have hp : (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.map) ∘ T.projection = S.projection :=
    funext p.over_ball
  change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback T.projection _
    (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.map) _ α.val) = _
  rw [← Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback_comp]
  apply Subtype.ext
  change α.val.val.pullback ((ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.map) ∘ T.projection) =
    α.val.val.pullback S.projection
  rw [hp]

theorem refinement_form_cup_nonzero (p : Cm.PrincipalRefinement K S T)
    (α β : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms S.surface.variety.analyticModel S.surface.variety.analyticSpace 2)
    (hn : S.surface.evaluate (Cm.cup S.surface.variety 2 2
      (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass S.surface.variety 2 α)
      (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass S.surface.variety 2 (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm β))) ≠ 0) :
    T.surface.evaluate (Cm.cup T.surface.variety 2 2
      (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass T.surface.variety 2 (projectiveClosedPullback p.map 2 α))
      (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass T.surface.variety 2
        (ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateClosedForm (projectiveClosedPullback p.map 2 β)))) ≠ 0 := by
  have h := p.evaluate_pullback_ne_zero _ hn
  rwa [Betti.CM.cup_pullback p.map 2 2, projective_form_class_pullback, projective_form_class_pullback,
    projective_closed_pullback_conjugate] at h

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RefinementForms.CM
