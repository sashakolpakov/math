import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.FramedRegularMapGluing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RegularGaugeGluing

/-! # Regular Map Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RegularMapGluing

noncomputable section

/-! Pointwise compatibility of actual regular coefficients in native
line frames gives a global algebraic morphism, with its local formulas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance nativeRegularMapGluing_integral : IsIntegral V.toOver.left := V.property
local instance nativeRegularMapGluing_smooth : Smooth V.toOver.hom := V.presentation.smooth

def nativeFramedRegularMap (L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier) (U : V.carrier.Opens)
    (r : LineFrameAtlas.LocalLineFrame L.sheaf) (s : LineFrameAtlas.LocalLineFrame K.sheaf)
    (hr : U ≤ r.domain) (hs : U ≤ s.domain) (a : Γ(V.carrier, U)) :
    L.sheaf.over U ⟶ K.sheaf.over U :=
  FramedRegularMapGluing.framedRegularMap L.sheaf K.sheaf U
    (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso L.sheaf U (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hr r.frame))
    (SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso K.sheaf U (SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization hs s.frame)) a

theorem exists_morphism_of_native_regular_coefficients (L K : HilbertConstruction.Line.Bundles.LineBundle V.carrier)
    {I : Type} (U : I → V.carrier.Opens) (hU : iSup U = ⊤)
    (r : I → LineFrameAtlas.LocalLineFrame L.sheaf) (s : I → LineFrameAtlas.LocalLineFrame K.sheaf)
    (hr : ∀ i, U i ≤ (r i).domain) (hs : ∀ i, U i ≤ (s i).domain)
    (c : ∀ i, Γ(V.carrier, U i))
    (hc : ∀ i j (x : V.analyticSpace) (hi : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ U i)
      (hj : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying x ∈ U j),
      AnalyticFrameTransitions.framePointTransition V.presentation (r i) (r j) x (hr i hi) (hr j hj) *
        RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left (U i) hi (c i) =
      RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue x.left (U j) hj (c j) *
        AnalyticFrameTransitions.framePointTransition V.presentation (s i) (s j) x (hs i hi) (hs j hj)) :
    ∃ f : L.sheaf ⟶ K.sheaf, ∀ i,
      f.over (U i) = nativeFramedRegularMap V L K (U i) (r i) (s i) (hr i) (hs i) (c i) := by
  let a (i j : I) : Γ(V.carrier, U i ⊓ U j) :=
    (r i).transition (r j) (U i ⊓ U j) (inf_le_left.trans (hr i)) (inf_le_right.trans (hr j))
  let b (i j : I) : Γ(V.carrier, U i ⊓ U j) :=
    (s i).transition (s j) (U i ⊓ U j) (inf_le_left.trans (hs i)) (inf_le_right.trans (hs j))
  let e i := SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hr i) (r i).frame
  let g i := SheafCohomology.Projective.OpenFrames.Scheme.Modules.restrictOpenTrivialization (hs i) (s i).frame
  have he : ∀ i j, _ := fun i j =>
    SheafCohomology.Projective.OverFrameScalarTransfer.overTrivializationOfRestrictIso_hom_eq_comp_scalar L.sheaf (U i ⊓ U j) _ _ (a i j)
      (RestrictedFrameTransition.restrictedFrame_transition (r i) (r j) (U i) (U j) (hr i) (hr j))
  have hg : ∀ i j, _ := fun i j =>
    SheafCohomology.Projective.OverFrameScalarTransfer.overTrivializationOfRestrictIso_hom_eq_comp_scalar K.sheaf (U i ⊓ U j) _ _ (b i j)
      (RestrictedFrameTransition.restrictedFrame_transition (s i) (s j) (U i) (U j) (hs i) (hs j))
  simp only [SheafCohomology.Projective.OpenFrames.Scheme.Modules.overTrivializationOfRestrictOpenTrivialization] at he hg
  apply FramedRegularMapGluing.exists_morphism_of_framed_regular_sections L.sheaf K.sheaf U hU
    (fun i => SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso L.sheaf (U i) (e i))
    (fun i => SheafCohomology.Projective.Invertible.Scheme.Modules.overTrivializationOfRestrictIso K.sheaf (U i) (g i)) c a b he hg
  intro i j
  apply RepresentationTheory.Theta.Geometric.Complex.PointsDetectSections.complexSectionValue_ext V.toOver (U i ⊓ U j)
  intro x hx
  erw [map_mul, map_mul, RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue_restrict, RepresentationTheory.Theta.Geometric.Complex.SectionEvaluation.complexSectionValue_restrict]
  have hL := (AnalyticFrameTransitions.framePointTransition_restrict V.presentation (r i) (r j) (U i ⊓ U j)
    (inf_le_left.trans (hr i)) (inf_le_right.trans (hr j)) ⟨x, hx⟩).trans
    (FrameEvaluation.sectionEvaluationOn_native V.presentation (U i ⊓ U j) (a i j) ⟨x, hx⟩)
  have hK := (AnalyticFrameTransitions.framePointTransition_restrict V.presentation (s i) (s j) (U i ⊓ U j)
    (inf_le_left.trans (hs i)) (inf_le_right.trans (hs j)) ⟨x, hx⟩).trans
    (FrameEvaluation.sectionEvaluationOn_native V.presentation (U i ⊓ U j) (b i j) ⟨x, hx⟩)
  erw [← hL, ← hK]
  exact hc i j x hx.1 hx.2

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.RegularMapGluing
