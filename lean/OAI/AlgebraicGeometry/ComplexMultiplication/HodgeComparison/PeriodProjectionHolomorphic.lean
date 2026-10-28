import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPeriodPrimitives
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodLattice
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-! # Period Projection Holomorphic -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodProjectionHolomorphic.CM.Construction

noncomputable section

/-! The actual projection to the period space takes the normalized
primitive vectors to holomorphic local maps. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

theorem mdifferentiable_finite_coordinates
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M]
    {ι : Type} [Fintype ι] (f : M → ι → ℂ)
    (hf : ∀ i, MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (fun x => f x i)) :
    MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) f := by
  intro x
  apply (mdifferentiableAt_iff _ x).mpr
  refine ⟨continuousAt_pi.mpr (fun i => (hf i x).continuousAt), ?_⟩
  have h (i : ι) := (hf i x).differentiableWithinAt_writtenInExtChartAt
  simp only [writtenInExtChartAt, mfld_simps] at h ⊢
  exact differentiableWithinAt_pi.mpr h

theorem zeroFormScalar_complex_sum
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace M] [ChartedSpace E M]
    {ι : Type} [Fintype ι] (t : ι → ℂ) (f : ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) (x : M) :
    HolomorphicPrimitive.CM.Construction.zeroFormScalar (∑ i, t i • f i) x = ∑ i, t i * HolomorphicPrimitive.CM.Construction.zeroFormScalar (f i) x := by
  let ev : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0 →ₗ[ℂ] ℂ :=
    { toFun := fun g => HolomorphicPrimitive.CM.Construction.zeroFormScalar g x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  change ev (∑ i, t i • f i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact map_smul ev (t i) (f i)

theorem rationalPeriodProjection_coordinate (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ (V.rationalCohomology 1))
    (j : Fin (Module.finrank ℂ (Module.Dual ℂ (RationalCoordinates.CM.Construction.rationalH1HolomorphicCoordinates V b)))) :
    ∃ t : RationalCoordinates.CM.Construction.rationalH1HolomorphicCoordinates V b, ∀ r : ι → ℂ,
      PeriodLattice.CM.Construction.rationalPeriodProjection V b r j = ∑ i, t.val i * r i := by
  let A : Module.Dual ℂ (Module.Dual ℂ (RationalCoordinates.CM.Construction.rationalH1HolomorphicCoordinates V b)) :=
    (LinearMap.proj j).comp (PeriodLattice.CM.Construction.rationalPeriodComplexEquiv V b).toLinearMap
  let t := (Module.evalEquiv ℂ (RationalCoordinates.CM.Construction.rationalH1HolomorphicCoordinates V b)).symm A
  refine ⟨t, ?_⟩
  intro r
  have h := Module.apply_evalEquiv_symm_apply ℂ (RationalCoordinates.CM.Construction.rationalH1HolomorphicCoordinates V b)
    (PeriodCoordinateDuality.CM.Construction.complexCoordinateEvaluation (RationalCoordinates.CM.Construction.rationalH1HolomorphicCoordinates V b) r) A
  change (∑ i, r i * t.val i) = PeriodLattice.CM.Construction.rationalPeriodProjection V b r j at h
  exact h.symm.trans (Finset.sum_congr rfl (fun i _ => mul_comm _ _))

theorem rationalPeriodProjection_primitives_holomorphic (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℚ (V.rationalCohomology 1))
    (U : Opens V.analyticSpace) (d : ℤ)
    (f : ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel U 0)
    (hf : ∀ i, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f i) =
      d • Intersection.CM.Construction.restrictSmoothForm U 1 (CanonicalRealOneForms.CM.Construction.canonicalRationalOneRepresentative V (b i)).val) :
    MDifferentiable 𝓘(ℂ, V.analyticModel) 𝓘(ℂ, PeriodLattice.CM.Construction.RationalH1PeriodSpace V b)
      (fun x : U => PeriodLattice.CM.Construction.rationalPeriodProjection V b (fun i => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f i) x)) := by
  apply mdifferentiable_finite_coordinates
  intro j
  obtain ⟨t, ht⟩ := rationalPeriodProjection_coordinate V b j
  have htype : (∑ i, t.val i • (V.rationalCohomologyInclusion 1 (b i) : V.complexCohomology 1)) ∈
      V.pureBettiSubspace 1 0 := by
    let qC : ι → V.complexCohomology 1 := fun i => V.rationalCohomologyInclusion 1 (b i)
    change (∑ i, t.val i • qC i) ∈ V.pureBettiSubspace 1 0
    have h := t.property
    change (RationalCoordinates.CM.Construction.rationalH1ComplexBasis V b).equivFun.symm t.val ∈ V.pureBettiSubspace 1 0 at h
    rw [Module.Basis.equivFun_symm_apply] at h
    have heq : (∑ i, t.val i • RationalCoordinates.CM.Construction.rationalH1ComplexBasis V b i) = ∑ i, t.val i • qC i := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun c : V.complexCohomology 1 => t.val i • c) (RationalCoordinates.CM.Construction.rationalH1ComplexBasis_apply V b i)
    exact heq ▸ h
  have hh := HolomorphicPeriodPrimitives.CM.Construction.holomorphic_period_primitive V (fun i => b i) U d f hf t.val htype
  have heq : (fun x : U => PeriodLattice.CM.Construction.rationalPeriodProjection V b (fun i => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f i) x) j) =
      HolomorphicPrimitive.CM.Construction.zeroFormScalar (∑ i, t.val i • f i) := by
    funext x
    rw [zeroFormScalar_complex_sum]
    exact ht _
  rwa [heq]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodProjectionHolomorphic.CM.Construction
