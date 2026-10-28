import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionLocalFrames
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.AnalyticFrameTransitions

/-! # Section Frame Evaluation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionFrameEvaluation

noncomputable section

/-! Actual section-frame transitions on complex points are evaluations
of the original regular section ratios. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem sectionEvaluationOn_topIso_hom (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (W : P.carrier.Opens)
    (a : Γ(W.toScheme, ⊤)) (p : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen P W) :
    DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P W (W.topIso.hom a) p =
      DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openPointHomeomorph P W).symm p) a :=
  congrArg (DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openPointHomeomorph P W).symm p))
    (ConcreteCategory.congr_hom W.topIso.hom_inv_id a)

theorem sectionFrame_pointTransition (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) {M : P.carrier.Modules}
    (s t : HilbertConstruction.Line.Bundles.structureModule P.carrier ⟶ M) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints P.toOver)
    (hs : p ∈ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen P (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s))
    (ht : p ∈ DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen P (HilbertConstruction.Ample.LineBundles.sectionNonvanishing t)) :
    AnalyticFrameTransitions.framePointTransition P (SectionLocalFrames.sectionLocalFrame s) (SectionLocalFrames.sectionLocalFrame t) p hs ht =
      DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation ((DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openPointHomeomorph P (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s)).symm ⟨p, hs⟩)
        (HilbertConstruction.Section.Frames.sectionRatio s t) := by
  let W := HilbertConstruction.Ample.LineBundles.sectionNonvanishing s ⊓ HilbertConstruction.Ample.LineBundles.sectionNonvanishing t
  let q : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.analyticOpen P W := ⟨p, hs, ht⟩
  let z := (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openPointHomeomorph P W).symm q
  have hz : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openRestriction P (show W ≤ HilbertConstruction.Ample.LineBundles.sectionNonvanishing s from inf_le_left)) z =
      (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openPointHomeomorph P (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s)).symm ⟨p, hs⟩ := by
    apply (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openPointHomeomorph P (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s)).injective
    rw [DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openPointHomeomorph_restrict, Homeomorph.apply_symm_apply]
    exact ((DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openPointHomeomorph P (HilbertConstruction.Ample.LineBundles.sectionNonvanishing s)).apply_symm_apply ⟨p, hs⟩).symm
  have h := congrArg (fun a : Γ(P.carrier, W) => DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn P W a q)
    (SectionLocalFrames.sectionLocalFrame_transition s t W inf_le_left inf_le_right)
  exact h.trans ((sectionEvaluationOn_topIso_hom P W _ q).trans
    ((DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation_map (DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openRestriction P (show W ≤ HilbertConstruction.Ample.LineBundles.sectionNonvanishing s from inf_le_left)) z
      (HilbertConstruction.Section.Frames.sectionRatio s t)).symm.trans
        (congrArg (fun a => DivisorClass.Chern.AnalyticTransitions.Construction.globalSectionEvaluation a (HilbertConstruction.Section.Frames.sectionRatio s t)) hz)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SectionFrameEvaluation
