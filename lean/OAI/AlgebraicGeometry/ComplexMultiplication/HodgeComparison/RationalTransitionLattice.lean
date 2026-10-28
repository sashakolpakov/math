import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PrimitiveTransitions
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodDenominators

/-! # Rational Transition Lattice -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalTransitionLattice.CM.Construction

noncomputable section

/-! Rational normalization and compact overlap cores put all transition
periods in one rescaling of a full rational lattice. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

def rationalPrimitiveTransition {U V : Opens M} (r : U → ℚ) (s : V → ℚ) :
    (U ⊓ V : Opens M) → ℚ :=
  fun x => r ⟨x.val, x.property.1⟩ - s ⟨x.val, x.property.2⟩

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem rationalPrimitiveTransition_cast {U V : Opens M}
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U 0) (g : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E V 0)
    (r : U → ℚ) (s : V → ℚ) (offset : M → ℂ)
    (hr : ∀ x, HolomorphicPrimitive.CM.Construction.zeroFormScalar f x = (r x : ℂ) + offset x.val)
    (hs : ∀ x, HolomorphicPrimitive.CM.Construction.zeroFormScalar g x = (s x : ℂ) + offset x.val)
    (x : (U ⊓ V : Opens M)) :
    (rationalPrimitiveTransition r s x : ℂ) = PrimitiveTransitions.CM.Construction.primitiveTransition f g x := by
  unfold rationalPrimitiveTransition PrimitiveTransitions.CM.Construction.primitiveTransition
  rw [hr, hs, Rat.cast_sub]
  ring

theorem rationalPrimitiveTransition_locallyConstant {U V : Opens M}
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U 0) (g : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E V 0)
    (hf : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f = Intersection.CM.Construction.restrictSmoothForm U 1 a)
    (hg : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d g = Intersection.CM.Construction.restrictSmoothForm V 1 a)
    (r : U → ℚ) (s : V → ℚ) (offset : M → ℂ)
    (hr : ∀ x, HolomorphicPrimitive.CM.Construction.zeroFormScalar f x = (r x : ℂ) + offset x.val)
    (hs : ∀ x, HolomorphicPrimitive.CM.Construction.zeroFormScalar g x = (s x : ℂ) + offset x.val) :
    IsLocallyConstant (rationalPrimitiveTransition r s) := by
  have hc := PrimitiveTransitions.CM.Construction.primitiveTransition_locallyConstant a f g hf hg
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  exact (hc.eventually_eq x).mono (fun y hy => by
    have hcast : (rationalPrimitiveTransition r s y : ℂ) =
        (rationalPrimitiveTransition r s x : ℂ) :=
      (rationalPrimitiveTransition_cast f g r s offset hr hs y).trans
        (hy.trans (rationalPrimitiveTransition_cast f g r s offset hr hs x).symm)
    exact_mod_cast hcast)

theorem normalized_transition_common_lattice [T2Space M]
    {ι κ J : Type} [Finite ι] [Finite κ] [Finite J]
    (basis : Module.Basis κ ℚ (ι → ℚ))
    (U : J → Opens M) (K : J → Set M) (hK : ∀ j, IsCompact (K j))
    (hKU : ∀ j, K j ⊆ U j)
    (a : ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1)
    (f : ∀ j, ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E (U j) 0)
    (hf : ∀ j i, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f j i) = Intersection.CM.Construction.restrictSmoothForm (U j) 1 (a i))
    (r : ∀ j, U j → ι → ℚ) (offset : M → ι → ℂ)
    (hr : ∀ j (x : U j) i, HolomorphicPrimitive.CM.Construction.zeroFormScalar (f j i) x = (r j x i : ℂ) + offset x.val i) :
    ∃ d : ℤ, 0 < d ∧ ∀ (j k : J) (x : M) (hxj : x ∈ K j) (hxk : x ∈ K k),
      d • (fun i => r j ⟨x, hKU j hxj⟩ i - r k ⟨x, hKU k hxk⟩ i) ∈
        Submodule.span ℤ (Set.range basis) := by
  let P (j k : J) : (K j ∩ K k : Set M) → (ι → ℚ) := fun x i =>
    r j ⟨x.val, hKU j x.property.1⟩ i - r k ⟨x.val, hKU k x.property.2⟩ i
  have hfinite (j k : J) : (Set.range (P j k)).Finite := by
    let : CompactSpace (K j ∩ K k : Set M) := isCompact_iff_compactSpace.mp ((hK j).inter (hK k))
    apply IsLocallyConstant.range_finite
    apply PrimitiveTransitions.CM.Construction.finite_coordinate_locallyConstant
    intro i
    exact (rationalPrimitiveTransition_locallyConstant (a i) (f j i) (f k i) (hf j i) (hf k i)
      (fun x => r j x i) (fun x => r k x i) (fun x => offset x i)
      (fun x => hr j x i) (fun x => hr k x i)).comp_continuous
        (continuous_subtype_val.subtype_mk (fun x => ⟨hKU j x.property.1, hKU k x.property.2⟩))
  let S : Set (ι → ℚ) := ⋃ j, ⋃ k, Set.range (P j k)
  have hS : S.Finite := Set.finite_iUnion (fun j => Set.finite_iUnion (hfinite j))
  obtain ⟨d, hd, h⟩ := PeriodDenominators.CM.Construction.finite_rational_periods_integer_multiple basis S hS
  refine ⟨d, hd, ?_⟩
  intro j k x hxj hxk
  exact h (P j k ⟨x, hxj, hxk⟩)
    (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨k, ⟨⟨x, hxj, hxk⟩, rfl⟩⟩⟩)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalTransitionLattice.CM.Construction
