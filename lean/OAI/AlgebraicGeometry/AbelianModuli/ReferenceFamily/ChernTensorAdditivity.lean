import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CommonLineFrames
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DoubleLogRefinement
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernLogAdditivity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.ChernComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.LineBundles

/-! # Chern Tensor Additivity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernTensorAdditivity

noncomputable section

/-! The native rational first Chern class adds on the actual HilbertConstruction tensor
product of line bundles. A common frame atlas and simultaneous logarithms
derive the formula, including all frame and cover comparisons. -/

open _root_.CategoryTheory _root_.TopologicalSpace

theorem lineBundleChernClass_tensor (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (L M : HilbertConstruction.Line.Bundles.LineBundle X.carrier) :
    Intrinsic.ChernClasses.lineBundleChernClass X (L.tensor M) = Intrinsic.ChernClasses.lineBundleChernClass X L + Intrinsic.ChernClasses.lineBundleChernClass X M := by
  let I := CommonLineFrames.CommonLineFrame L.sheaf M.sheaf
  let U (i : I) := AnalyticFrameTransitions.frameAnalyticOpen X i.left
  have hU : ∀ p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver, ∃ i, p ∈ U i := by
    intro p
    obtain ⟨i, hi⟩ := CommonLineFrames.commonLineFrames_cover L M (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p)
    exact ⟨i, hi⟩
  let g (i j : I) : C((U i ⊓ U j : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)), ℂ) :=
    AnalyticFrameTransitions.frameTransitionPair X i.left j.left
  let h (i j : I) : C((U i ⊓ U j : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)), ℂ) :=
    AnalyticFrameTransitions.frameTransitionPair X i.right j.right
  let D := Classical.choice (DoubleLogRefinement.nonempty_doubleLogarithmicRefinement U hU g h
    (fun i j p => AnalyticFrameTransitions.frameTransitionPair_ne_zero X i.left j.left p)
    (fun i j p => AnalyticFrameTransitions.frameTransitionPair_ne_zero X i.right j.right p))
  let T := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
  let l : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain T D.cover := fun a => (D.leftLog (a 0) (a 1)).comp
    (DivisorClass.Chern.LogRefinementOpen.Construction.openInclusionMap (DivisorClass.Chern.BundleLogarithms.Construction.cechIntersection_le_pair D.cover a))
  let m : DivisorClass.Chern.LogCech.RationalCech.LogCechCochain T D.cover := fun a => (D.rightLog (a 0) (a 1)).comp
    (DivisorClass.Chern.LogRefinementOpen.Construction.openInclusionMap (DivisorClass.Chern.BundleLogarithms.Construction.cechIntersection_le_pair D.cover a))
  let r (i : D.Index) := (D.parent i).left
  let s (i : D.Index) := (D.parent i).right
  let t (i : D.Index) := (D.parent i).tensor
  have hr : ∀ i, D.cover i ≤ AnalyticFrameTransitions.frameAnalyticOpen X (r i) := D.subset
  have hs : ∀ i, D.cover i ≤ AnalyticFrameTransitions.frameAnalyticOpen X (s i) := D.subset
  have ht : ∀ i, D.cover i ≤ AnalyticFrameTransitions.frameAnalyticOpen X (t i) := D.subset
  have hl : ∀ (a : Fin 2 → D.Index) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection D.cover a),
      Complex.exp (l a p) = AnalyticFrameTransitions.framePointTransition X (r (a 0)) (r (a 1)) p.val
        (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le D.cover a 0 p.property))
        (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le D.cover a 1 p.property)) := by
    intro a p
    exact D.left_exp (a 0) (a 1) ⟨p.val, DivisorClass.Chern.BundleLogarithms.Construction.cechIntersection_le_pair D.cover a p.property⟩
  have hm : ∀ (a : Fin 2 → D.Index) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection D.cover a),
      Complex.exp (m a p) = AnalyticFrameTransitions.framePointTransition X (s (a 0)) (s (a 1)) p.val
        (hs (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le D.cover a 0 p.property))
        (hs (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le D.cover a 1 p.property)) := by
    intro a p
    exact D.right_exp (a 0) (a 1) ⟨p.val, DivisorClass.Chern.BundleLogarithms.Construction.cechIntersection_le_pair D.cover a p.property⟩
  have hlc := Frame.ChernComparison.frameLog_exponentialCocycle D.cover r hr l hl
  have hmc := Frame.ChernComparison.frameLog_exponentialCocycle D.cover s hs m hm
  have htc := ChernLogAdditivity.exponentialCocycle_add T D.cover l m hlc hmc
  have htm : ∀ (a : Fin 2 → D.Index) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection D.cover a),
      Complex.exp ((l + m) a p) = AnalyticFrameTransitions.framePointTransition X (t (a 0)) (t (a 1)) p.val
        (ht (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le D.cover a 0 p.property))
        (ht (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le D.cover a 1 p.property)) := by
    intro a p
    change Complex.exp (l a p + m a p) = _
    rw [Complex.exp_add, hl, hm]
    exact (CommonLineFrames.commonLineFrame_tensor_transition (D.parent (a 0)) (D.parent (a 1)) p.val _ _).symm
  unfold Intrinsic.ChernClasses.lineBundleChernClass
  rw [Frame.ChernComparison.firstChernClass_eq_frameLogs (Intrinsic.ChernClasses.nativeLineBundle X (L.tensor M)) D.cover D.covers t ht (l + m) htc htm,
    Frame.ChernComparison.firstChernClass_eq_frameLogs (Intrinsic.ChernClasses.nativeLineBundle X L) D.cover D.covers r hr l hlc hl,
    Frame.ChernComparison.firstChernClass_eq_frameLogs (Intrinsic.ChernClasses.nativeLineBundle X M) D.cover D.covers s hs m hmc hm]
  exact ChernLogAdditivity.logarithmicSingularClass_add T D.cover D.covers l m hlc hmc

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernTensorAdditivity
