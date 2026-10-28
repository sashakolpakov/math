import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntegralPrimitiveCover
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.ContinuousMap.Basic

/-! # Period Map Gluing -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodMapGluing.CM.Construction

noncomputable section

/-! Actual local primitive vectors with integer transitions glue after
passing to a quotient by a subgroup containing those periods. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {ι J T : Type} [AddCommGroup T] [TopologicalSpace T]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem glue_integer_primitive_maps (U : J → Opens M)
    (hcover : ∀ x : M, ∃ j, x ∈ U j)
    (f : ∀ j, ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E (U j) 0)
    (hf : ∀ (j k : J) (x : M) (hxj : x ∈ U j) (hxk : x ∈ U k),
      ∃ z : ι → ℤ, ∀ i, PrimitiveTransitions.CM.Construction.primitiveTransition (f j i) (f k i) ⟨x, hxj, hxk⟩ = (z i : ℂ))
    (L : (ι → ℂ) →+ T) (hL : Continuous L) (Λ : AddSubgroup T)
    (hΛ : ∀ z : ι → ℤ, L (fun i => (z i : ℂ)) ∈ Λ) :
    ∃ p : C(M, T ⧸ Λ), ∀ j (x : U j),
      p x.val = QuotientAddGroup.mk (L (fun i => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f j i) x)) := by
  let φ (j : J) : C(U j, T ⧸ Λ) :=
    ⟨fun x => QuotientAddGroup.mk (L (fun i => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f j i) x)),
      QuotientAddGroup.continuous_mk.comp
        (hL.comp (continuous_pi (fun i => Intersection.CM.Construction.zeroFormScalar_continuous (f j i))))⟩
  have hφ (j k : J) (x : M) (hxj : x ∈ U j) (hxk : x ∈ U k) :
      φ j ⟨x, hxj⟩ = φ k ⟨x, hxk⟩ := by
    obtain ⟨z, hz⟩ := hf j k x hxj hxk
    apply sub_eq_zero.mp
    change (QuotientAddGroup.mk (L (fun i => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f j i) ⟨x, hxj⟩)) : T ⧸ Λ) -
      QuotientAddGroup.mk (L (fun i => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f k i) ⟨x, hxk⟩)) = 0
    rw [← QuotientAddGroup.mk_sub, ← map_sub]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    have heq : (fun i => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f j i) ⟨x, hxj⟩) -
        (fun i => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f k i) ⟨x, hxk⟩) = fun i => (z i : ℂ) :=
      funext hz
    rw [heq]
    exact hΛ z
  have hnhds : ∀ x : M, ∃ j, (U j : Set M) ∈ nhds x := by
    intro x
    obtain ⟨j, hj⟩ := hcover x
    exact ⟨j, (U j).isOpen.mem_nhds hj⟩
  refine ⟨ContinuousMap.liftCover (fun j => (U j : Set M)) φ hφ hnhds, ?_⟩
  intro j x
  exact ContinuousMap.liftCover_coe (S := fun j => (U j : Set M))
    (φ := φ) (hφ := hφ) (hS := hnhds) x

theorem projective_period_map (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {ι T : Type} [Fintype ι] [AddCommGroup T] [TopologicalSpace T]
    (q : ι → V.rationalCohomology 1)
    (a : ι → Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)
    (ha : ∀ i, (V.deRhamBettiIso 1).hom (V.deRhamClass 1 (a i)) =
      V.rationalCohomologyInclusion 1 (q i))
    (L : (ι → ℂ) →+ T) (hL : Continuous L) (Λ : AddSubgroup T)
    (hΛ : ∀ z : ι → ℤ, L (fun i => (z i : ℂ)) ∈ Λ) :
    ∃ (d : ℤ), 0 < d ∧ ∃ p : C(V.analyticSpace, T ⧸ Λ),
      ∀ x : V.analyticSpace, ∃ (U : Opens V.analyticSpace), x ∈ U ∧
        ∃ f : ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel U 0,
          (∀ i, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f i) = d • Intersection.CM.Construction.restrictSmoothForm U 1 (a i).val) ∧
          ∀ y : U, p y.val = QuotientAddGroup.mk (L (fun i => HolomorphicPrimitive.CM.Construction.zeroFormScalar (f i) y)) := by
  obtain ⟨d, hd, s, U, hcover, f, hf, hperiod⟩ := IntegralPrimitiveCover.CM.Construction.projective_integral_primitive_cover V q a ha
  obtain ⟨p, hp⟩ := glue_integer_primitive_maps U hcover f hperiod L hL Λ hΛ
  refine ⟨d, hd, p, ?_⟩
  intro x
  obtain ⟨j, hj⟩ := hcover x
  exact ⟨U j, hj, f j, hf j, hp j⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodMapGluing.CM.Construction
