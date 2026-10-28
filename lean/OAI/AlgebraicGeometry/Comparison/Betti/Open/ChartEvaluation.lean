import OAI.AlgebraicGeometry.Comparison.Betti.Open.FiltrationDescent
import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ManifoldBidegree

/-! # Chart Evaluation -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.ChartEvaluation.Hodge

noncomputable section

section

/-! The existing smooth type projectors on open sections have exactly
the chartwise bidegrees used by the actual local Dolbeault theorem. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff BigOperators

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

def openPureFormsInDegree (U : Opens M) (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) :
    Submodule ℂ (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :=
  (ManifoldFormFiltration.Hodge.pureFormsInDegree E U n i).comap (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).toLinearMap

theorem mem_openPureFormsInDegree_iff (U : Opens M) (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    a ∈ openPureFormsInDegree U n i ↔ DivisorClass.Chern.Open.ManifoldBidegree.OpenManifoldHasBidegree i.val.1 i.val.2 a := by
  rcases i with ⟨⟨p, q⟩, hi⟩
  subst n
  change Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E U p q (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (p + q) a).val ↔ _
  rw [IntrinsicPurity.Holomorphic.intrinsicOpenFormEquiv_pure_iff]
  constructor
  · intro h e he y hy
    exact h e he y hy.1 hy.2
  · intro h e he y hy hyU
    exact h e he y ⟨hy, hyU⟩

theorem openPureFormsInDegree_mem_filtration (U : Opens M) (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
    (r : ℤ) (hr : r ≤ (i.val.1 : ℤ)) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n)
    (ha : a ∈ openPureFormsInDegree U n i) : a ∈ FiltrationDescent.Hodge.openFormFiltration U n r := by
  change Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n a ∈ ManifoldFormFiltration.Hodge.manifoldFormFiltration E U n r
  exact Submodule.mem_iSup_of_mem i (Submodule.mem_iSup_of_mem hr ha)

theorem openTypeProjection_pure [FiniteDimensional ℝ E]
    (U : Opens M) (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    FiltrationDescent.Hodge.openTypeProjection U n i a ∈ openPureFormsInDegree U n i := by
  change Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n (FiltrationDescent.Hodge.openTypeProjection U n i a) ∈ ManifoldFormFiltration.Hodge.pureFormsInDegree E U n i
  simp only [FiltrationDescent.Hodge.openTypeProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  exact ManifoldFormFiltration.Hodge.manifoldTypeProjection_pure E U n i _

theorem openTypeProjection_identity (U : Opens M) (n : ℕ) (i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (ha : a ∈ openPureFormsInDegree U n i) :
    FiltrationDescent.Hodge.openTypeProjection U n i a = a := by
  apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).injective
  simp only [FiltrationDescent.Hodge.openTypeProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  exact ManifoldFormFiltration.Hodge.manifoldTypeProjection_identity E U n i _ ha

theorem openTypeProjection_other (U : Opens M) (n : ℕ) (i j : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n) (hij : i ≠ j)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (ha : a ∈ openPureFormsInDegree U n j) :
    FiltrationDescent.Hodge.openTypeProjection U n i a = 0 := by
  apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).injective
  simp only [FiltrationDescent.Hodge.openTypeProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, map_zero]
  exact ManifoldFormFiltration.Hodge.manifoldTypeProjection_other E U n i j hij _ ha

theorem sum_openTypeProjection [FiniteDimensional ℝ E]
    (U : Opens M) (n : ℕ) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    ∑ i : Analysis.HodgeTheory.Decomposition.Core.Constructions.Bidegree n, FiltrationDescent.Hodge.openTypeProjection U n i a = a := by
  apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U n).injective
  simp only [map_sum, FiltrationDescent.Hodge.openTypeProjection, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply]
  exact ManifoldFormFiltration.Hodge.sum_manifoldTypeProjection E U n _

end

/-! Linear chart evaluation and joint faithfulness for actual smooth
open manifold forms. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℂ, E) ∞ M]

def openChartEvaluation (U : Opens M) (n : ℕ) (e : OpenPartialHomeomorph M E) (y : E) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n where
  toFun a := a.extension.inChart e y
  map_add' a b := by
    rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_add, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add]
    rfl
  map_smul' c a := by
    rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_smul, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_smul]
    rfl

theorem openForm_eq_of_inChart {U : Opens M} {n : ℕ} {a b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n}
    (h : ∀ (e : OpenPartialHomeomorph M E), e ∈ atlas E M →
      ∀ y ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e (U : Set M),
        a.extension.inChart e y = b.extension.inChart e y) : a = b := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  let e := chartAt E (x : M)
  have he : e ∈ atlas E M := chart_mem_atlas E (x : M)
  have hx : (x : M) ∈ e.source := mem_chart_source E (x : M)
  have hdom : e x ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e (U : Set M) :=
    ⟨e.map_source hx, by
      change e.symm (e x) ∈ U
      simpa only [e.left_inv hx] using x.property⟩
  have hc := h e he (e x) hdom
  have hv := (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart_inChart_apply e he a.extension hx).symm.trans
    ((congrArg (fun c : Analysis.DifferentialForms.Manifold.Basic.FormValue E n => c.compContinuousLinearMap (Analysis.DifferentialForms.Manifold.Charts.chartTangentMap e x)) hc).trans
      (Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.fromChart_inChart_apply e he b.extension hx))
  simpa only [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply] using hv

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.ChartEvaluation.Hodge
