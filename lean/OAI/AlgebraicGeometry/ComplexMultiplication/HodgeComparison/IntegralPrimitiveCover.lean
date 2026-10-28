import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalPrimitiveCover
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalTransitionLattice
import Mathlib.LinearAlgebra.StdBasis

/-! # Integral Primitive Cover -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntegralPrimitiveCover.CM.Construction

noncomputable section

/-! A single positive integer clears every transition period of a finite
rational family. The resulting actual local primitives differ by integer vectors. -/

open _root_.CategoryTheory _root_.TopologicalSpace Set

theorem integer_span_coordinate_values {ι : Type} [Fintype ι]
    (v : ι → ℚ) (hv : v ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℚ ι))) :
    ∃ z : ι → ℤ, ∀ i, (v i : ℂ) = (z i : ℂ) := by
  classical
  have h (i : ι) : ∃ z : ℤ, (z : ℚ) = v i := by
    obtain ⟨z, hz⟩ := ((Pi.basisFun ℚ ι).mem_span_iff_repr_mem ℤ v).mp hv i
    refine ⟨z, ?_⟩
    rw [Pi.basisFun_repr, algebraMap_int_eq] at hz
    exact hz
  choose z hz using h
  refine ⟨z, fun i => ?_⟩
  exact_mod_cast (hz i).symm

theorem projective_integral_primitive_cover (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {ι : Type} [Fintype ι] (q : ι → V.rationalCohomology 1)
    (a : ι → Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)
    (ha : ∀ i, (V.deRhamBettiIso 1).hom (V.deRhamClass 1 (a i)) =
      V.rationalCohomologyInclusion 1 (q i)) :
    ∃ (d : ℤ), 0 < d ∧ ∃ (s : Finset V.analyticSpace) (U : s → Opens V.analyticSpace),
      (∀ x : V.analyticSpace, ∃ j, x ∈ U j) ∧
      ∃ f : ∀ j, ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel (U j) 0,
        (∀ j i, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f j i) = d • Intersection.CM.Construction.restrictSmoothForm (U j) 1 (a i).val) ∧
        ∀ (j k : s) (x : V.analyticSpace) (hxj : x ∈ U j) (hxk : x ∈ U k),
          ∃ z : ι → ℤ, ∀ i,
            PrimitiveTransitions.CM.Construction.primitiveTransition (f j i) (f k i) ⟨x, hxj, hxk⟩ = (z i : ℂ) := by
  classical
  obtain ⟨s, U, W, hcover, hWU, hcompact, f, r, offset, hf, hr⟩ :=
    RationalPrimitiveCover.CM.Construction.projective_rational_primitive_cover V q a ha
  obtain ⟨d, hd, hperiod⟩ := RationalTransitionLattice.CM.Construction.normalized_transition_common_lattice (Pi.basisFun ℚ ι) U
    (fun j => closure (W j : Set V.analyticSpace)) hcompact hWU
    (fun i => (a i).val) f hf r offset hr
  have hsub (j : s) : W j ≤ U j := subset_closure.trans (hWU j)
  let g (j : s) (i : ι) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel (W j) 0 :=
    d • PrimitiveTransitions.CM.Construction.localFormRestriction (hsub j) 0 (f j i)
  have hg (j : s) (i : ι) : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (g j i) =
      d • Intersection.CM.Construction.restrictSmoothForm (W j) 1 (a i).val := by
    rw [map_zsmul, PrimitiveTransitions.CM.Construction.localFormRestriction_d, hf, PrimitiveTransitions.CM.Construction.localFormRestriction_global]
  refine ⟨d, hd, s, W, hcover, g, hg, ?_⟩
  intro j k x hxj hxk
  let v : ι → ℚ := d • (fun i =>
    r j ⟨x, hsub j hxj⟩ i - r k ⟨x, hsub k hxk⟩ i)
  obtain ⟨z, hz⟩ := integer_span_coordinate_values v
    (hperiod j k x (subset_closure hxj) (subset_closure hxk))
  refine ⟨z, fun i => ?_⟩
  have hc : d • ((r j ⟨x, hsub j hxj⟩ i - r k ⟨x, hsub k hxk⟩ i : ℚ) : ℂ) =
      (z i : ℂ) := by
    have hi := hz i
    change ((d • (r j ⟨x, hsub j hxj⟩ i - r k ⟨x, hsub k hxk⟩ i) : ℚ) : ℂ) = _ at hi
    exact (map_zsmul (Rat.castHom ℂ) d _).symm.trans hi
  change d • HolomorphicPrimitive.CM.Construction.zeroFormScalar (PrimitiveTransitions.CM.Construction.localFormRestriction (hsub j) 0 (f j i)) ⟨x, hxj⟩ -
    d • HolomorphicPrimitive.CM.Construction.zeroFormScalar (PrimitiveTransitions.CM.Construction.localFormRestriction (hsub k) 0 (f k i)) ⟨x, hxk⟩ = _
  rw [PrimitiveTransitions.CM.Construction.localFormRestriction_scalar, PrimitiveTransitions.CM.Construction.localFormRestriction_scalar, ← smul_sub]
  have heq : HolomorphicPrimitive.CM.Construction.zeroFormScalar (f j i) ⟨x, hsub j hxj⟩ -
      HolomorphicPrimitive.CM.Construction.zeroFormScalar (f k i) ⟨x, hsub k hxk⟩ =
      ((r j ⟨x, hsub j hxj⟩ i - r k ⟨x, hsub k hxk⟩ i : ℚ) : ℂ) := by
    rw [hr, hr, Rat.cast_sub]
    ring
  rw [heq]
  exact hc

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.IntegralPrimitiveCover.CM.Construction
