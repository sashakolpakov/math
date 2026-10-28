import OAI.AlgebraicGeometry.DivisorClass.Chern.Regular.FrameChern
import OAI.AlgebraicGeometry.DivisorClass.Chern.LogGauge

/-! # Frame Trivial -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Regular

noncomputable section

/-! A single global regular frame gives zero for the original algebraic first Chern class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open OAI.AlgebraicGeometry.DivisorClass.Chern.LogGauge.RationalCech
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} {L : Line.Bundles.AlgebraicLineBundle P} {ι : Type}
  (A : FrameAnalyticTransitions.RegularSectionFrameAtlas L ι)

theorem FrameAnalyticTransitions.RegularSectionFrameAtlas.pointTransition_self (i : ι) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) (hi : p ∈ A.analyticDomain i) :
    A.pointTransition i i p hi hi = 1 := by
  have ht : A.transition i i (A.domain i) le_rfl le_rfl = 1 := by
    apply Units.ext
    change A.frame i (A.domain i) le_rfl ((A.frame i (A.domain i) le_rfl).symm 1) = 1
    exact (A.frame i (A.domain i) le_rfl).apply_symm_apply 1
  have he : Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P (A.domain i) (1 : Γ(P.carrier, A.domain i)) ⟨p, hi⟩ = 1 := by
    change AnalyticTransitions.Construction.globalSectionEvaluation ((Line.Bundles.AlgebraicLineBundle.openPointHomeomorph P (A.domain i)).symm ⟨p, hi⟩)
      ((A.domain i).topIso.inv 1) = 1
    rw [map_one, map_one]
  exact (A.pointTransition_restrict i i (A.domain i) le_rfl le_rfl ⟨p, hi⟩).trans
    ((congrArg (fun t : Γ(P.carrier, A.domain i)ˣ => Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P (A.domain i)
      (t : Γ(P.carrier, A.domain i)) ⟨p, hi⟩) ht).trans he)

theorem FrameAnalyticTransitions.RegularSectionFrameAtlas.firstChernClassQ_zero_of_global_frame (i : ι)
    (hi : ∀ p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver, p ∈ A.analyticDomain i) : First.firstChernClassQ P L = 0 := by
  let U : Unit → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver) := fun _ => ⊤
  have hU : ∀ p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver, ∃ a, p ∈ U a := fun _ => ⟨(), trivial⟩
  have hsub : ∀ a : Unit, U a ≤ A.analyticDomain i := fun _ p _ => hi p
  have hc := A.firstChernClassQ_eq_on_cover U hU (fun _ => i) hsub 0
    (LogGauge.RationalCech.exponentialCocycle_zero (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)) U) (by
      intro a p
      simpa only [Pi.zero_apply, ContinuousMap.zero_apply, Complex.exp_zero] using
        (A.pointTransition_self i p.val (hi p.val)).symm)
  exact hc.symm.trans (LogGauge.RationalCech.logarithmicSingularClass_zero (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)) U hU)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Regular
