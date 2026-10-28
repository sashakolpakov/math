import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPeriodMap
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientTangentCoordinates

/-! # Smooth Period Map -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothPeriodMap.CM.Construction

noncomputable section

/-! The constructed period map is real smooth, directly from its smooth
local primitives. This supplies the actual pullback on differential forms. -/

open _root_.TopologicalSpace Filter
open scoped _root_.Manifold ContDiff _root_.Topology

open scoped OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientManifold.CM.Construction.ComplexLatticeQuotient

theorem zeroFormScalar_contMDiff
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (HolomorphicPrimitive.CM.Construction.zeroFormScalar f) := by
  intro x
  let e := chartAt E x
  have hx : x ∈ e.source := mem_chart_source E x
  have he : e ∈ atlas E M := chart_mem_atlas E x
  have hf := HolomorphicPrimitive.CM.Construction.zeroFormScalar_contDiffAt_inChart f e he (e.map_source hx)
  have hc : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ e x :=
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞) he) hx
  have heq : (HolomorphicPrimitive.CM.Construction.zeroFormScalar f ∘ e.symm) ∘ e =ᶠ[𝓝 x] HolomorphicPrimitive.CM.Construction.zeroFormScalar f := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact congrArg (HolomorphicPrimitive.CM.Construction.zeroFormScalar f) (e.left_inv hy)
  exact heq.contMDiffAt_iff.mp (hf.comp_contMDiffAt hc)

theorem contMDiff_finite_coordinates
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    {ι : Type} [Fintype ι] (f : M → ι → ℂ)
    (hf : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (fun x => f x i)) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ι → ℂ) ∞ f := by
  intro x
  apply contMDiffAt_iff.mpr
  refine ⟨continuousAt_pi.mpr (fun i => (hf i x).continuousAt), ?_⟩
  have h (i : ι) := (contMDiffAt_iff.mp (hf i x)).2
  simp only [mfld_simps] at h ⊢
  exact contDiffWithinAt_pi.mpr h

theorem realOpenInverse_contMDiffAt
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    (U : Opens M) (hs : Nonempty U) {x : M} (hx : x ∈ U) :
    ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (U.openPartialHomeomorphSubtypeCoe hs).symm x := by
  rw [← ContMDiffAt.subtypeVal_comp_iff]
  apply contMDiffAt_id.congr_of_eventuallyEq
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  exact (U.openPartialHomeomorphSubtypeCoe hs).right_inv
    (by simpa only [Opens.openPartialHomeomorphSubtypeCoe_target] using hy)

theorem contMDiff_of_open_restrictions
    {E F M N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]
    (f : M → N)
    (hf : ∀ x : M, ∃ U : Opens M, x ∈ U ∧
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ (fun y : U => f y.val)) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f := by
  intro x
  obtain ⟨U, hx, hU⟩ := hf x
  let hs : Nonempty U := ⟨⟨x, hx⟩⟩
  let e := U.openPartialHomeomorphSubtypeCoe hs
  have hg := (hU (e.symm x)).comp x (realOpenInverse_contMDiffAt U hs hx)
  have heq : ((fun y : U => f y.val) ∘ e.symm) =ᶠ[𝓝 x] f := by
    filter_upwards [U.isOpen.mem_nhds hx] with y hy
    exact congrArg f (e.right_inv (by
      simpa only [e, Opens.openPartialHomeomorphSubtypeCoe_target] using hy))
  exact heq.contMDiffAt_iff.mp hg

theorem rationalPeriodProjection_primitives_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ (V.rationalCohomology 1))
    (U : Opens V.analyticSpace) (f : ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel U 0) :
    ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, PeriodLattice.CM.Construction.RationalH1PeriodSpace V b) ∞
      (fun x : U => PeriodLattice.CM.Construction.rationalPeriodProjection V b (fun i => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f i) x)) := by
  exact (PeriodLattice.CM.Construction.rationalPeriodProjection V b).restrictScalars ℝ |>.contDiff.comp_contMDiff
    (contMDiff_finite_coordinates _ (fun i => zeroFormScalar_contMDiff (f i)))

theorem exists_smooth_holomorphic_rationalH1_period_map (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ (V.rationalCohomology 1)) :
    ∃ d : ℤ, 0 < d ∧ ∃ p : C(V.analyticSpace, PeriodLattice.CM.Construction.RationalH1PeriodTorus V b),
      MDifferentiable 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, PeriodLattice.CM.Construction.RationalH1PeriodSpace V b) p ∧
      ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, PeriodLattice.CM.Construction.RationalH1PeriodSpace V b) ∞ p ∧
      ∀ x : V.analyticSpace, ∃ U : Opens V.analyticSpace, x ∈ U ∧
        ∃ f : ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel U 0,
          (∀ i, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f i) =
            d • Intersection.CM.Construction.restrictSmoothForm U 1 (CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative V (b i)).val) ∧
          ∀ y : U, p y.val = QuotientAddGroup.mk
            (PeriodLattice.CM.Construction.rationalPeriodProjection V b (fun i => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f i) y)) := by
  obtain ⟨d, hd, p, hp, hlocal⟩ := HolomorphicPeriodMap.CM.Construction.exists_holomorphic_rationalH1_period_map V b
  refine ⟨d, hd, p, hp, ?_, hlocal⟩
  apply contMDiff_of_open_restrictions
  intro x
  obtain ⟨U, hx, f, _, hU⟩ := hlocal x
  refine ⟨U, hx, ?_⟩
  have hπ := QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient.projection_realContMDiff
    (PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup
  have hcomp := hπ.comp (rationalPeriodProjection_primitives_smooth V b U f)
  have heq : (fun y : U => p y.val) = fun y : U =>
      (QuotientAddGroup.mk
        (PeriodLattice.CM.Construction.rationalPeriodProjection V b (fun i => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f i) y)) : PeriodLattice.CM.Construction.RationalH1PeriodTorus V b) :=
    funext hU
  rw [heq]
  exact hcomp

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothPeriodMap.CM.Construction
