import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalLp
import OAI.Analysis.DifferentialForms.Manifold.FinitePartition
import OAI.Analysis.DifferentialForms.Manifold.FunctionMultiplication

/-! # Smooth Representative Gluing -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothRepresentativeGluing.CM.Construction

noncomputable section

/-! Local smooth representatives of one global L2 function patch to a
single actual smooth zero-form using a finite smooth partition of unity. -/

open _root_.MeasureTheory Set Filter
open scoped _root_.Manifold

theorem smooth_representative_of_local_germs (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Lp ℂ 2 (GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V))
    (hlocal : ∀ x : V.analyticSpace, ∃ U : Set V.analyticSpace,
      IsOpen U ∧ x ∈ U ∧ ∃ f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0,
        u =ᵐ[(GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V).restrict U] HolomorphicPrimitive.CM.Construction.zeroFormScalar f) :
    ∃ f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0, GlobalLp.CM.Construction.varietySmoothScalarL2 V f = u := by
  classical
  choose U hU hx f hf using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU (by
    intro x _
    exact mem_iUnion.mpr ⟨x, hx x⟩)
  have hcover : ∀ x : V.analyticSpace, ∃ i : s, x ∈ U i.val := by
    intro x
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    exact ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨ψ, hψ, hψU, hsum⟩ := Analysis.DifferentialForms.Manifold.FinitePartition.exists_finite_complex_partition
    (E := V.analyticModel) (fun i : s => U i.val) (fun i => hU i.val) hcover
  let g : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0 :=
    ∑ i : s, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction (ψ i) (hψ i) (f i.val)
  have hgs (x : V.analyticSpace) : HolomorphicPrimitive.CM.Construction.zeroFormScalar g x =
      ∑ i : s, ψ i x * HolomorphicPrimitive.CM.Construction.zeroFormScalar (f i.val) x := by
    let L : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace 0 →ₗ[ℂ] ℂ :=
      { toFun := fun q => HolomorphicPrimitive.CM.Construction.zeroFormScalar q x
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    change L (∑ i : s, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.smulByFunction (ψ i) (hψ i) (f i.val)) = _
    rw [map_sum]
    rfl
  have hae : ∀ᵐ x ∂ GlobalMetricMeasure.CM.Construction.varietyMetricMeasure V, ∀ i : s, x ∈ U i.val → u x = HolomorphicPrimitive.CM.Construction.zeroFormScalar (f i.val) x :=
    ae_all_iff.mpr (fun i => (ae_restrict_iff' (hU i.val).measurableSet).mp (hf i.val))
  refine ⟨g, Lp.ext ?_⟩
  filter_upwards [GlobalLp.CM.Construction.varietySmoothScalarL2_coe V g, hae] with x hgx hfx
  rw [hgx, hgs]
  calc
    _ = ∑ i : s, ψ i x * u x := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : ψ i x = 0
      · rw [hi, zero_mul, zero_mul]
      · rw [hfx i (hψU i (subset_tsupport (ψ i) hi))]
    _ = (∑ i : s, ψ i x) * u x := Finset.sum_mul .. |>.symm
    _ = u x := by rw [hsum, one_mul]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothRepresentativeGluing.CM.Construction
