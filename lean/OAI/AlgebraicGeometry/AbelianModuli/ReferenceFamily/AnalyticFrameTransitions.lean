import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas

/-! # Analytic Frame Transitions -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticFrameTransitions

noncomputable section

/-! Evaluate every genuine local frame transition on the native complex
point space. The resulting continuous units satisfy the cocycle and
change-of-frame equations on actual common algebraic opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {M : X.carrier.Modules}

def frameAnalyticOpen (s : LineFrameAtlas.LocalLineFrame M) := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X s.domain

def frameTransitionPair (s t : LineFrameAtlas.LocalLineFrame M) :
    C((frameAnalyticOpen X s ⊓ frameAnalyticOpen X t : TopologicalSpace.Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)), ℂ) :=
  DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X (s.domain ⊓ t.domain) (s.transition t _ inf_le_left inf_le_right : Γ(X.carrier, _))

theorem frameTransitionPair_ne_zero (s t : LineFrameAtlas.LocalLineFrame M)
    (p : (frameAnalyticOpen X s ⊓ frameAnalyticOpen X t : TopologicalSpace.Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))) :
    frameTransitionPair X s t p ≠ 0 := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_unit_ne_zero X _ _ _

abbrev framePointTransition (s t : LineFrameAtlas.LocalLineFrame M) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
    (hs : p ∈ frameAnalyticOpen X s) (ht : p ∈ frameAnalyticOpen X t) : ℂ :=
  frameTransitionPair X s t ⟨p, hs, ht⟩

theorem framePointTransition_restrict (s t : LineFrameAtlas.LocalLineFrame M) (U : X.carrier.Opens)
    (hs : U ≤ s.domain) (ht : U ≤ t.domain) (p : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U) :
    framePointTransition X s t p.val (hs p.property) (ht p.property) =
      DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U (s.transition t U hs ht : Γ(X.carrier, U)) p := by
  have hU : U ≤ s.domain ⊓ t.domain := le_inf hs ht
  have he := DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict X hU
    (s.transition t (s.domain ⊓ t.domain) inf_le_left inf_le_right : Γ(X.carrier, _)) p
  have h := congrArg Units.val (s.transition_restrict t hU inf_le_left inf_le_right)
  change X.carrier.presheaf.map (homOfLE hU).op
    (s.transition t (s.domain ⊓ t.domain) inf_le_left inf_le_right : Γ(X.carrier, _)) =
      (s.transition t U hs ht : Γ(X.carrier, U)) at h
  rw [h] at he
  exact he.symm

theorem framePointTransition_cocycle (s t r : LineFrameAtlas.LocalLineFrame M)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) (hs : p ∈ frameAnalyticOpen X s)
    (ht : p ∈ frameAnalyticOpen X t) (hr : p ∈ frameAnalyticOpen X r) :
    framePointTransition X s t p hs ht * framePointTransition X t r p ht hr =
      framePointTransition X s r p hs hr := by
  let U := (s.domain ⊓ t.domain) ⊓ r.domain
  have hUs : U ≤ s.domain := inf_le_left.trans inf_le_left
  have hUt : U ≤ t.domain := inf_le_left.trans inf_le_right
  have hUr : U ≤ r.domain := inf_le_right
  let q : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen X U := ⟨p, ⟨hs, ht⟩, hr⟩
  have h := congrArg (fun u : Γ(X.carrier, U)ˣ => DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U (u : Γ(X.carrier, U)) q)
    (s.transition_cocycle t r U hUs hUt hUr)
  change DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U
    ((s.transition t U hUs hUt : Γ(X.carrier, U)) * (t.transition r U hUt hUr : Γ(X.carrier, U))) q = _ at h
  rw [DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_mul, ← framePointTransition_restrict,
    ← framePointTransition_restrict, ← framePointTransition_restrict] at h
  exact h

theorem framePointTransition_gauge (s t u v : LineFrameAtlas.LocalLineFrame M)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) (hs : p ∈ frameAnalyticOpen X s)
    (ht : p ∈ frameAnalyticOpen X t) (hu : p ∈ frameAnalyticOpen X u)
    (hv : p ∈ frameAnalyticOpen X v) :
    framePointTransition X u v p hu hv =
      framePointTransition X s t p hs ht * framePointTransition X t v p ht hv /
        framePointTransition X s u p hs hu := by
  apply (eq_div_iff (frameTransitionPair_ne_zero X s u ⟨p, hs, hu⟩)).mpr
  rw [mul_comm, framePointTransition_cocycle, framePointTransition_cocycle]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticFrameTransitions
