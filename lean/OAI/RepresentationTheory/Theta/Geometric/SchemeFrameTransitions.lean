import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas
import OAI.RepresentationTheory.Theta.Geometric.SchemeSectionNaturality

/-! # Scheme Frame Transitions -/

namespace OAI.RepresentationTheory.Theta.Geometric.SchemeFrameTransitions

noncomputable section

/-! Evaluate every genuine local frame transition on the native complex
point space. The resulting continuous units satisfy the cocycle and
change-of-frame equations on actual common algebraic opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.RepresentationTheory.Theta.Geometric.SchemeSectionNaturality.SchemeSectionEvaluation
open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas (LocalLineFrame)

namespace SchemeFrames

variable (X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) {M : X.left.Modules}

def frameAnalyticOpen (s : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame M) := SchemeSectionNaturality.SchemeSectionEvaluation.analyticOpen X s.domain

def frameTransitionPair (s t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame M) :
    C((frameAnalyticOpen X s ⊓ frameAnalyticOpen X t : TopologicalSpace.Opens (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)), ℂ) :=
  SchemeSectionNaturality.SchemeSectionEvaluation.sectionEvaluationOn X (s.domain ⊓ t.domain) (s.transition t _ inf_le_left inf_le_right : Γ(X.left, _))

theorem frameTransitionPair_ne_zero (s t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame M)
    (p : (frameAnalyticOpen X s ⊓ frameAnalyticOpen X t : TopologicalSpace.Opens (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))) :
    frameTransitionPair X s t p ≠ 0 := SchemeSectionNaturality.SchemeSectionEvaluation.sectionEvaluationOn_unit_ne_zero X _ _ _

abbrev framePointTransition (s t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame M) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (hs : p ∈ frameAnalyticOpen X s) (ht : p ∈ frameAnalyticOpen X t) : ℂ :=
  frameTransitionPair X s t ⟨p, hs, ht⟩

theorem framePointTransition_restrict (s t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame M) (U : X.left.Opens)
    (hs : U ≤ s.domain) (ht : U ≤ t.domain) (p : SchemeSectionNaturality.SchemeSectionEvaluation.analyticOpen X U) :
    framePointTransition X s t p.val (hs p.property) (ht p.property) =
      SchemeSectionNaturality.SchemeSectionEvaluation.sectionEvaluationOn X U (s.transition t U hs ht : Γ(X.left, U)) p := by
  have hU : U ≤ s.domain ⊓ t.domain := le_inf hs ht
  have he := SchemeSectionNaturality.SchemeSectionEvaluation.sectionEvaluationOn_restrict X hU
    (s.transition t (s.domain ⊓ t.domain) inf_le_left inf_le_right : Γ(X.left, _)) p
  have h := congrArg Units.val (s.transition_restrict t hU inf_le_left inf_le_right)
  change X.left.presheaf.map (homOfLE hU).op
    (s.transition t (s.domain ⊓ t.domain) inf_le_left inf_le_right : Γ(X.left, _)) =
      (s.transition t U hs ht : Γ(X.left, U)) at h
  rw [h] at he
  exact he.symm

theorem framePointTransition_cocycle (s t r : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame M)
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hs : p ∈ frameAnalyticOpen X s)
    (ht : p ∈ frameAnalyticOpen X t) (hr : p ∈ frameAnalyticOpen X r) :
    framePointTransition X s t p hs ht * framePointTransition X t r p ht hr =
      framePointTransition X s r p hs hr := by
  let U := (s.domain ⊓ t.domain) ⊓ r.domain
  have hUs : U ≤ s.domain := inf_le_left.trans inf_le_left
  have hUt : U ≤ t.domain := inf_le_left.trans inf_le_right
  have hUr : U ≤ r.domain := inf_le_right
  let q : SchemeSectionNaturality.SchemeSectionEvaluation.analyticOpen X U := ⟨p, ⟨hs, ht⟩, hr⟩
  have h := congrArg (fun u : Γ(X.left, U)ˣ => SchemeSectionNaturality.SchemeSectionEvaluation.sectionEvaluationOn X U (u : Γ(X.left, U)) q)
    (s.transition_cocycle t r U hUs hUt hUr)
  change SchemeSectionNaturality.SchemeSectionEvaluation.sectionEvaluationOn X U
    ((s.transition t U hUs hUt : Γ(X.left, U)) * (t.transition r U hUt hUr : Γ(X.left, U))) q = _ at h
  rw [SchemeSectionNaturality.SchemeSectionEvaluation.sectionEvaluationOn_mul, ← framePointTransition_restrict,
    ← framePointTransition_restrict, ← framePointTransition_restrict] at h
  exact h

theorem framePointTransition_gauge (s t u v : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame M)
    (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) (hs : p ∈ frameAnalyticOpen X s)
    (ht : p ∈ frameAnalyticOpen X t) (hu : p ∈ frameAnalyticOpen X u)
    (hv : p ∈ frameAnalyticOpen X v) :
    framePointTransition X u v p hu hv =
      framePointTransition X s t p hs ht * framePointTransition X t v p ht hv /
        framePointTransition X s u p hs hu := by
  apply (eq_div_iff (frameTransitionPair_ne_zero X s u ⟨p, hs, hu⟩)).mpr
  rw [mul_comm, framePointTransition_cocycle, framePointTransition_cocycle]

end SchemeFrames

end

end OAI.RepresentationTheory.Theta.Geometric.SchemeFrameTransitions
