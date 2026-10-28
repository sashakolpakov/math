import OAI.AlgebraicGeometry.Comparison.Betti.Open.ChartEvaluation
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.FilteredSections

/-! # Top Filtered Forms -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.TopFilteredForms.Hodge

noncomputable section

/-! The top smooth filtration consists of the pure holomorphic type.
Closed sections give sections of the original holomorphic de Rham complex. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

theorem topFiltered_openPure (U : Opens M) (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n)
    (ha : a ∈ Open.FiltrationDescent.Hodge.openFormFiltration U n (n : ℤ)) :
    a ∈ Open.ChartEvaluation.Hodge.openPureFormsInDegree U n ⟨(n, 0), Nat.add_zero n⟩ := by
  have hle : ManifoldFormFiltration.Hodge.manifoldFormFiltration E U n (n : ℤ) ≤
      ManifoldFormFiltration.Hodge.pureFormsInDegree E U n ⟨(n, 0), Nat.add_zero n⟩ := by
    refine iSup_le fun i => iSup_le fun hi => ?_
    have he : i = ⟨(n, 0), Nat.add_zero n⟩ := by
      apply Subtype.ext
      have hsum := i.property
      apply Prod.ext
      · change i.val.1 = n
        omega
      · change i.val.2 = 0
        omega
    rw [he]
  exact hle ha

theorem closed_topFiltered_holomorphic (U : Opens M) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (ha : a ∈ Open.FiltrationDescent.Hodge.openFormFiltration U n (n : ℤ))
    (hd : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a = 0) :
    ∃ A : Holomorphic.DeRhamComplex.forms E U n, Holomorphic.LocalDescent.ambientHolomorphicInclusion U n A = a ∧ Holomorphic.DeRhamComplex.differential E U n A = 0 := by
  have hp := topFiltered_openPure U n a ha
  let ap : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E U n 0 := ⟨Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n a, hp⟩
  have hda : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n a) = 0 := by
    rw [Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_d, hd, map_zero]
  have hhol : ap ∈ Holomorphic.DeRhamComplex.forms E U n := by
    apply (Holomorphic.DeRhamComplex.mem_forms_iff_derivative_pure n ap).mpr
    change Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E U (n + 1) 0 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n a)).val
    rw [hda]
    exact (Analysis.DifferentialForms.Manifold.ManifoldBidegree.pureManifoldFormSubmodule E U (n + 1) 0).zero_mem
  let A : Holomorphic.DeRhamComplex.forms E U n := ⟨ap, hhol⟩
  refine ⟨A, ?_, ?_⟩
  · change (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).symm (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n a) = a
    exact LinearEquiv.symm_apply_apply _ a
  · apply Holomorphic.HolomorphicPullback.inclusion_injective (n + 1)
    rw [Holomorphic.DeRhamComplex.inclusion_differential, map_zero]
    exact hda

theorem ambientHolomorphicInclusion_d (U : Opens M) (n : ℕ) (a : Holomorphic.DeRhamComplex.forms E U n) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Holomorphic.LocalDescent.ambientHolomorphicInclusion U n a) =
      Holomorphic.LocalDescent.ambientHolomorphicInclusion U (n + 1) (Holomorphic.DeRhamComplex.differential E U n a) := by
  apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (n + 1)).injective
  change Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (n + 1)
      (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).symm (Holomorphic.DeRhamComplex.inclusion E U n a))) =
    Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (n + 1) ((Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (n + 1)).symm
      (Holomorphic.DeRhamComplex.inclusion E U (n + 1) (Holomorphic.DeRhamComplex.differential E U n a)))
  rw [← Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_d, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, Holomorphic.DeRhamComplex.inclusion_differential]

end

end OAI.AlgebraicGeometry.Comparison.Betti.TopFilteredForms.Hodge
