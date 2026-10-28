import OAI.AlgebraicGeometry.Comparison.Betti.LocalHolomorphicPurity

/-! # Intrinsic Purity -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.IntrinsicPurity.Holomorphic

noncomputable section

section

/-! Intrinsic pure type on an open submanifold is exactly ambient chartwise pure type on that open. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {U : Opens M} {p q : ℕ}

theorem intrinsicOpenFormEquiv_pure_iff (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (p + q)) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E U p q (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (p + q) a).val ↔
      ∀ e ∈ atlas E M, ∀ y ∈ e.target, e.symm y ∈ U →
        Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q (a.extension.inChart e y) := by
  constructor
  · intro ha e he y hy hyU
    let hs : Nonempty U := ⟨⟨e.symm y, hyU⟩⟩
    let g := (U.openPartialHomeomorphSubtypeCoe hs).symm
    let form := (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (p + q) a).val
    let f := chartAt E (g (e.symm y))
    have hf : f ∈ atlas E U := chart_mem_atlas E (g (e.symm y))
    have hfy : g (e.symm y) ∈ f.source := mem_chart_source E (g (e.symm y))
    have hex : a.extension (e.symm y) = form.pullback (E := E) g (e.symm y) := by
      have h := Analysis.DifferentialForms.Manifold.IntrinsicOpenTangent.intrinsicOpenRawEquiv_symm_extension hs form hyU
      change Analysis.DifferentialForms.Manifold.Open.openManifoldFormExtension U ((Analysis.DifferentialForms.Manifold.IntrinsicOpenTangent.intrinsicOpenRawEquiv U (p + q)).symm
        (Analysis.DifferentialForms.Manifold.IntrinsicOpenTangent.intrinsicOpenRawEquiv U (p + q) a.val)) (e.symm y) = _ at h
      rw [LinearEquiv.symm_apply_apply] at h
      exact h
    have heq : a.extension.inChart e y = (form.pullback (E := E) g).inChart e y := by
      change (a.extension (e.symm y)).compContinuousLinearMap _ =
        (form.pullback (E := E) g (e.symm y)).compContinuousLinearMap _
      rw [hex]
    rw [heq]
    exact LocalHolomorphicPurity.pure_pullback_inChart_at form g e f he hf hy hfy
      (LocalHolomorphicPurity.complexOpenInverse_contMDiffAt hs hyU) (ha f hf (f (g (e.symm y))) (f.map_source hfy))
  · intro ha e he y hy
    let g := (Subtype.val : U → M)
    let f := chartAt E (g (e.symm y))
    have hf : f ∈ atlas E M := chart_mem_atlas E (g (e.symm y))
    have hfy : g (e.symm y) ∈ f.source := mem_chart_source E (g (e.symm y))
    change Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E p q ((Analysis.DifferentialForms.Manifold.IntrinsicOpenTangent.intrinsicOpenRawEquiv U (p + q) a.val).inChart e y)
    rw [Analysis.DifferentialForms.Manifold.IntrinsicOpenTangent.intrinsicOpenRawEquiv_eq_pullback]
    apply LocalHolomorphicPurity.pure_pullback_inChart_at a.extension g e f he hf hy hfy
      (contMDiff_subtype_val (I := 𝓘(ℂ, E)) (n := ∞) (e.symm y))
    apply ha f hf (f (g (e.symm y))) (f.map_source hfy)
    rw [f.left_inv hfy]
    exact (e.symm y).property

end

/-! The actual pure-type condition for forms is local under arbitrary open covers. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {U V : Opens M} {n p q : ℕ}

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M] in
theorem restrict_extension_inChart (h : V ≤ U) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n)
    (e : OpenPartialHomeomorph M E) (y : E) (hy : e.symm y ∈ V) :
    (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a).extension.inChart e y = a.extension.inChart e y := by
  change ((Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a).extension (e.symm y)).compContinuousLinearMap _ =
    (a.extension (e.symm y)).compContinuousLinearMap _
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply _ ⟨e.symm y, hy⟩,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_apply a ⟨e.symm y, h hy⟩]
  rfl

theorem intrinsic_pure_of_cover_restrict_pure {ι : Type} (V : ι → Opens M)
    (hsub : ∀ i, V i ≤ U) (hcover : (U : Set M) ⊆ ⋃ i, (V i : Set M))
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U (p + q))
    (ha : ∀ i, Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E (V i) p q
      (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E (V i) (p + q) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (hsub i) a)).val) :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E U p q (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U (p + q) a).val := by
  apply (intrinsicOpenFormEquiv_pure_iff (p := p) (q := q) a).mpr
  intro e he y hy hyU
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hyU)
  have hp := (intrinsicOpenFormEquiv_pure_iff (p := p) (q := q)
    (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (hsub i) a)).mp (ha i) e he y hy hi
  rw [restrict_extension_inChart (hsub i) a e y hi] at hp
  exact hp

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.IntrinsicPurity.Holomorphic
