import OAI.RepresentationTheory.Theta.Geometric.SchemeFrameTransitions
import OAI.RepresentationTheory.Theta.Geometric.CocyclePointValues
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticFrameTransitions

/-! # Scheme Atlas Frames -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The continuous cocycle of the actual scheme atlas is computed by
its actual local sheaf frames, including on smooth projective fibers. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.RepresentationTheory.Theta.Geometric.SchemeSectionNaturality.SchemeSectionEvaluation OAI.RepresentationTheory.Theta.Geometric.SchemeFrameTransitions.SchemeFrames

section
variable {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left} (A : SchemeLineFrame.SchemeLineAtlas L)

def SchemeLineFrame.SchemeLineAtlas.localFrame (i : X.left) : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame L.sheaf := ⟨A.domain i, A.frame i⟩

theorem SchemeLineFrame.SchemeLineAtlas.localFrame_transition (i j : X.left) (U : X.left.Opens)
    (hi : U ≤ A.domain i) (hj : U ≤ A.domain j) :
    (A.localFrame i).transition (A.localFrame j) U hi hj = A.transition i j U hi hj := rfl

theorem SchemeLineFrame.SchemeLineAtlas.pointTransition_restrict (i j : X.left) (W : X.left.Opens)
    (hi : W ≤ A.domain i) (hj : W ≤ A.domain j) (p : SchemeSectionNaturality.SchemeSectionEvaluation.analyticOpen X W) :
    A.continuousCocycle.pointTransition i j p.val (hi p.property) (hj p.property) =
      SchemeSectionNaturality.SchemeSectionEvaluation.sectionEvaluationOn X W (A.transition i j W hi hj : Γ(X.left, W)) p := by
  let a : Fin 2 → X.left := ![i, j]
  have hWA : W ≤ A.algebraicIntersection a := by
    intro z hz
    apply (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection A.domain a z).mpr
    intro k
    fin_cases k
    · exact hi hz
    · exact hj hz
  let u := A.transition i j (A.algebraicIntersection a)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le A.domain a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le A.domain a 1)
  have hu : X.left.presheaf.map (homOfLE hWA).op (u : Γ(X.left, A.algebraicIntersection a)) =
      (A.transition i j W hi hj : Γ(X.left, W)) :=
    congrArg Units.val (A.transition_restrict i j hWA
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le A.domain a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le A.domain a 1))
  have he := SchemeSectionNaturality.SchemeSectionEvaluation.sectionEvaluationOn_restrict X hWA (u : Γ(X.left, A.algebraicIntersection a)) p
  rw [hu] at he
  exact he.symm

theorem SchemeLineFrame.SchemeLineAtlas.pointTransition_eq_frame (i j : X.left) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    (hi : p ∈ A.analyticCover i) (hj : p ∈ A.analyticCover j) :
    A.continuousCocycle.pointTransition i j p hi hj =
      SchemeFrameTransitions.SchemeFrames.framePointTransition X (A.localFrame i) (A.localFrame j) p hi hj := by
  let W := A.domain i ⊓ A.domain j
  let q : SchemeSectionNaturality.SchemeSectionEvaluation.analyticOpen X W := ⟨p, hi, hj⟩
  exact (A.pointTransition_restrict i j W inf_le_left inf_le_right q).trans
    (SchemeFrameTransitions.SchemeFrames.framePointTransition_restrict X (A.localFrame i) (A.localFrame j) W
      inf_le_left inf_le_right q).symm

end

theorem SchemeAtlasFrames.schemeFrame_pointTransition_native (X : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    {M : X.carrier.Modules} (s t : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LineFrameAtlas.LocalLineFrame M) (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
    (hs : p ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen X s) (ht : p ∈ AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.frameAnalyticOpen X t) :
    SchemeFrameTransitions.SchemeFrames.framePointTransition X.toOver s t p hs ht = AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticFrameTransitions.framePointTransition X s t p hs ht := rfl

end

end OAI.RepresentationTheory.Theta.Geometric
