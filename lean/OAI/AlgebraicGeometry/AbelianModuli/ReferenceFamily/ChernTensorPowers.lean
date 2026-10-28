import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PowerFrameTransitions
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernLogAdditivity
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Frame.ChernComparison

/-! # Chern Tensor Powers -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernTensorPowers

noncomputable section

/-! Tensor-power scaling of the original native rational Chern class,
using the actual HilbertConstruction multilinear sheaf construction. -/

open _root_.CategoryTheory _root_.TopologicalSpace

theorem lineBundleChernClass_tensorPower (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (L : HilbertConstruction.Line.Bundles.LineBundle X.carrier) (n : ℕ) :
    Intrinsic.ChernClasses.lineBundleChernClass X (L.tensorPower n) = n • Intrinsic.ChernClasses.lineBundleChernClass X L := by
  let B := Intrinsic.ChernClasses.nativeLineBundle X L
  let U := B.logCover
  let T := TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
  let r (i : B.LogCoverIndex) := Frame.ChernComparison.chosenLineFrame B (B.logParent i)
  let t (i : B.LogCoverIndex) := (r i).power n
  have hr : ∀ i, U i ≤ AnalyticFrameTransitions.frameAnalyticOpen X (r i) := B.logCover_subset
  have ht : ∀ i, U i ≤ AnalyticFrameTransitions.frameAnalyticOpen X (t i) := B.logCover_subset
  have he : ∀ (a : Fin 2 → B.LogCoverIndex) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a),
      Complex.exp ((n • B.bundleLogCech) a p) =
        AnalyticFrameTransitions.framePointTransition X (t (a 0)) (t (a 1)) p.val
          (ht (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
          (ht (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property)) := by
    intro a p
    change Complex.exp (n • B.bundleLogCech a p) = _
    rw [Complex.exp_nsmul, B.bundleLogCech_exp_point]
    exact (congrArg (fun z : ℂ => z ^ n)
      (Frame.ChernComparison.chosenLineFrame_transition B (B.logParent (a 0)) (B.logParent (a 1)) p.val
        (hr (a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0 p.property))
        (hr (a 1) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1 p.property))).symm).trans
      (PowerFrameTransitions.powerFrame_pointTransition (r (a 0)) (r (a 1)) n p.val _ _).symm
  exact (Frame.ChernComparison.firstChernClass_eq_frameLogs (Intrinsic.ChernClasses.nativeLineBundle X (L.tensorPower n))
    U B.logCover_covers t ht (n • B.bundleLogCech)
    (ChernLogAdditivity.exponentialCocycle_nsmul T U B.bundleLogCech B.bundleLogCech_cocycle n) he).trans
      (ChernLogAdditivity.logarithmicSingularClass_nsmul T U B.logCover_covers
        B.bundleLogCech B.bundleLogCech_cocycle n)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ChernTensorPowers
