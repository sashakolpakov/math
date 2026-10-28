import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.HolomorphicSections
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.KaehlerGluing
import OAI.Analysis.DifferentialForms.Manifold.PurePullback

/-! # Open Purity -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OpenPurity.Kaehler

noncomputable section

/-! Pure type of the actual globally glued Kähler realization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology
open OAI.Analysis.DifferentialForms.Manifold.PurePullback

section OpenCharts

variable {F M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]

theorem onOpen_intrinsic_chart (U : Opens M) (n : ℕ)
    (form : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F M n) (u : U) :
    (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv F U n (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen U form)).val.inChart
        (chartAt F u) (chartAt F u u) =
      form.val.inChart (chartAt F u.val) (chartAt F u.val u.val) := by
  rw [Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_onOpen]
  let e := chartAt F u
  let f := chartAt F u.val
  let y := e u
  have hey : e.symm y = u := e.left_inv (mem_chart_source F u)
  have hf : (Subtype.val : U → M) (e.symm y) ∈ f.source := by
    rw [hey]
    exact mem_chart_source F u.val
  change (form.val.pullback (Subtype.val : U → M)).inChart e y = form.val.inChart f (f u.val)
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.pullback_inChart form.val (Subtype.val : U → M) e f
    (chart_mem_atlas F u) (chart_mem_atlas F u.val)
    (e.map_source (mem_chart_source F u)) hf
    ((contMDiff_subtype_val (I := 𝓘(ℝ, F)) (n := ∞)).mdifferentiableAt (by simp))]
  have hid : (f ∘ (Subtype.val : U → M) ∘ e.symm) =ᶠ[nhds y] id := by
    have hs := (U.chartAt_subtype_val_symm_eventuallyEq (H := F) (x := u)).symm
    filter_upwards [hs, f.open_target.mem_nhds (f.map_source (mem_chart_source F u.val))]
      with z hz hzt
    exact (congrArg f hz).trans (f.right_inv hzt)
  rw [Filter.EventuallyEq.fderiv_eq hid, fderiv_id]
  ext v
  exact congrArg (fun z : U => form.val.inChart f (f z.val) v) hey

end OpenCharts

attribute [local instance] Comparison.Betti.Algebraic.Sheaves.sectionAlgebra

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom] [X.left.IsSeparated]

omit [X.left.IsSeparated] in
theorem affineSmoothForm_intrinsic_pure (U : X.left.Opens) (hU : IsAffineOpen U)
    (form : AbelianScheme.TateComparison.FormConstants.OneForms X) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) 1 0
      (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) 1
        (Kaehler.affineSmoothForm X U hU form)).val := by
  change Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree _ _ 1 0
    ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) 1)
      ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) 1).symm
        (Comparison.Betti.Smooth.CochainMap.smoothFormMap (Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn X U) (Comparison.Betti.Open.SmoothEvaluation.sectionEvaluationOn_smooth X U)
          1 (Kaehler.affineForm X U hU form)))).val
  rw [LinearEquiv.apply_symm_apply, Comparison.Betti.Smooth.CochainMap.smoothFormMap_one]
  exact HolomorphicSections.Kaehler.algebraicOneForm_pure (Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn X U) (Comparison.Betti.Open.SmoothEvaluation.sectionEvaluationOn_smooth X U)
    (HolomorphicSections.Kaehler.sectionEvaluationOn_holomorphic X U) _

theorem globalSmoothForm_pure (form : AbelianScheme.TateComparison.FormConstants.OneForms X) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (Comparison.Betti.RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) 1 0
      (KaehlerGluing.globalSmoothForm X form).val := by
  apply (Analysis.DifferentialForms.Manifold.BidegreeInvariant.hasManifoldBidegree_iff_chartAt _).mpr
  intro p
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (KaehlerGluing.affineAnalytic_cover X (Set.mem_univ p))
  let u : Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X i.val := ⟨p, hi⟩
  have h := affineSmoothForm_intrinsic_pure X i.val i.property form
  rw [← KaehlerGluing.globalSmoothForm_onAffine X form i.val i.property] at h
  have hp := h (chartAt (Comparison.Betti.RegularSmoothness.NativeModel X) u) (chart_mem_atlas (Comparison.Betti.RegularSmoothness.NativeModel X) u)
    (chartAt (Comparison.Betti.RegularSmoothness.NativeModel X) u u)
    ((chartAt (Comparison.Betti.RegularSmoothness.NativeModel X) u).map_source (mem_chart_source (Comparison.Betti.RegularSmoothness.NativeModel X) u))
  rw [onOpen_intrinsic_chart] at hp
  exact hp

omit [X.left.IsSeparated] in
theorem affineSmoothForm_d_intrinsic_pure (U : X.left.Opens) (hU : IsAffineOpen U)
    (form : AbelianScheme.TateComparison.FormConstants.OneForms X) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) 2 0
      (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) 2
        (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Kaehler.affineSmoothForm X U hU form))).val := by
  change Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree _ _ 2 0
    (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) 2
      (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Comparison.Betti.Open.SmoothForms.openSmoothFormMap X U 1 (Kaehler.affineForm X U hU form)))).val
  rw [← Comparison.Betti.Open.SmoothForms.openSmoothFormMap_d]
  change Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree _ _ 2 0
    ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) 2)
      ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv (Comparison.Betti.RegularSmoothness.NativeModel X) (Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X U) 2).symm
        (Comparison.Betti.Smooth.CochainMap.smoothFormMap (Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn X U) (Comparison.Betti.Open.SmoothEvaluation.sectionEvaluationOn_smooth X U)
          2 (Comparison.Betti.Algebraic.Forms.differential Γ(X.left, U) 1 (Kaehler.affineForm X U hU form))))).val
  rw [LinearEquiv.apply_symm_apply]
  exact HolomorphicSections.Kaehler.algebraicTwoForm_pure (Comparison.Betti.Open.AffineIsoEvaluation.sectionEvaluationOn X U) (Comparison.Betti.Open.SmoothEvaluation.sectionEvaluationOn_smooth X U)
    (HolomorphicSections.Kaehler.sectionEvaluationOn_holomorphic X U) _

/-- Closedness reduces to vanishing of this actual exact (2,0) form. -/
theorem globalSmoothForm_d_pure (form : AbelianScheme.TateComparison.FormConstants.OneForms X) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree (Comparison.Betti.RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) 2 0
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (KaehlerGluing.globalSmoothForm X form)).val := by
  apply (Analysis.DifferentialForms.Manifold.BidegreeInvariant.hasManifoldBidegree_iff_chartAt _).mpr
  intro p
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (KaehlerGluing.affineAnalytic_cover X (Set.mem_univ p))
  let u : Comparison.Betti.Open.AffineIsoEvaluation.analyticOpen X i.val := ⟨p, hi⟩
  have h := affineSmoothForm_d_intrinsic_pure X i.val i.property form
  rw [← KaehlerGluing.globalSmoothForm_onAffine X form i.val i.property, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.onOpen_d] at h
  have hp := h (chartAt (Comparison.Betti.RegularSmoothness.NativeModel X) u) (chart_mem_atlas (Comparison.Betti.RegularSmoothness.NativeModel X) u)
    (chartAt (Comparison.Betti.RegularSmoothness.NativeModel X) u u)
    ((chartAt (Comparison.Betti.RegularSmoothness.NativeModel X) u).map_source (mem_chart_source (Comparison.Betti.RegularSmoothness.NativeModel X) u))
  rw [onOpen_intrinsic_chart] at hp
  exact hp

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OpenPurity.Kaehler
