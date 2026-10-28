import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.FrameEvaluation
import OAI.RepresentationTheory.Theta.Geometric.IntrinsicFrame.UnitGluing
import OAI.RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RestrictedFrameTransition

/-! # Regular Gauge Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RegularGaugeGluing

noncomputable section

/-! Actual regular comparison units satisfying their native pointwise
frame identity glue to an isomorphism of the original algebraic sheaves. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance regularGaugeGluing_integral : IsIntegral V.toOver.left := V.property
local instance regularGaugeGluing_smooth : Smooth V.toOver.hom := V.presentation.smooth

theorem exists_iso_of_native_regular_gauges (L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier)
    {I : Type} (U : I → V.carrier.Opens) (hU : iSup U = ⊤)
    (r : I → LineFrameAtlas.LocalLineFrame L.sheaf) (s : I → LineFrameAtlas.LocalLineFrame K.sheaf)
    (hr : ∀ i, U i ≤ (r i).domain) (hs : ∀ i, U i ≤ (s i).domain)
    (g : ∀ i, Γ(V.carrier, U i)ˣ)
    (hg : ∀ i j (x : V.analyticSpace) (hi : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ U i)
      (hj : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ U j),
      AnalyticFrameTransitions.framePointTransition V.presentation (r i) (r j) x (hr i hi) (hr j hj) *
        RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left (U i) hi (g i : Γ(V.carrier, U i)) =
      RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left (U j) hj (g j : Γ(V.carrier, U j)) *
        AnalyticFrameTransitions.framePointTransition V.presentation (s i) (s j) x (hs i hi) (hs j hj)) :
    Nonempty (L.sheaf ≅ K.sheaf) := by
  let a (i j : I) : Γ(V.carrier, U i ⊓ U j) :=
    (r i).transition (r j) (U i ⊓ U j) (inf_le_left.trans (hr i)) (inf_le_right.trans (hr j))
  let b (i j : I) : Γ(V.carrier, U i ⊓ U j) :=
    (s i).transition (s j) (U i ⊓ U j) (inf_le_left.trans (hs i)) (inf_le_right.trans (hs j))
  apply RepresentationTheory.Theta.Geometric.IntrinsicFrame.UnitGluing.exists_iso_of_open_framed_units L.sheaf K.sheaf U hU
    (fun i => SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hr i) (r i).frame)
    (fun i => SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hs i) (s i).frame) g a b
  · intro i j
    exact RestrictedFrameTransition.restrictedFrame_transition (r i) (r j) (U i) (U j) (hr i) (hr j)
  · intro i j
    exact RestrictedFrameTransition.restrictedFrame_transition (s i) (s j) (U i) (U j) (hs i) (hs j)
  · intro i j
    apply RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections.complexSectionValue_ext V.toOver (U i ⊓ U j)
    intro x hx
    erw [map_mul, map_mul, RepresentationTheory.Theta.Geometric.PowerGaugeCover.restrictRegularUnit_value, RepresentationTheory.Theta.Geometric.PowerGaugeCover.restrictRegularUnit_value]
    have hL := (AnalyticFrameTransitions.framePointTransition_restrict V.presentation (r i) (r j) (U i ⊓ U j)
      (inf_le_left.trans (hr i)) (inf_le_right.trans (hr j)) ⟨x, hx⟩).trans
      (FrameEvaluation.sectionEvaluationOn_native V.presentation (U i ⊓ U j) (a i j) ⟨x, hx⟩)
    have hK := (AnalyticFrameTransitions.framePointTransition_restrict V.presentation (s i) (s j) (U i ⊓ U j)
      (inf_le_left.trans (hs i)) (inf_le_right.trans (hs j)) ⟨x, hx⟩).trans
      (FrameEvaluation.sectionEvaluationOn_native V.presentation (U i ⊓ U j) (b i j) ⟨x, hx⟩)
    erw [← hL, ← hK]
    exact hg i j x hx.1 hx.2

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RegularGaugeGluing
