import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalCochainNormalization
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalIntegrationDefect

/-! # Rational Primitive Cover -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalPrimitiveCover.CM.Construction

noncomputable section

/-! Finite rational families admit genuine smooth local primitives whose
differences are rational. Normalization uses the actual singular comparison. -/

open _root_.CategoryTheory _root_.TopologicalSpace Set

theorem projective_rational_primitive_cover (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {ι : Type} [Finite ι] (q : ι → V.rationalCohomology 1)
    (a : ι → Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1)
    (ha : ∀ i, (V.deRhamBettiIso 1).hom (V.deRhamClass 1 (a i)) =
      V.rationalCohomologyInclusion 1 (q i)) :
    ∃ (s : Finset V.analyticSpace) (U W : s → Opens V.analyticSpace),
      (∀ x : V.analyticSpace, ∃ j, x ∈ W j) ∧
      (∀ j, closure (W j : Set V.analyticSpace) ⊆ U j) ∧
      (∀ j, IsCompact (closure (W j : Set V.analyticSpace))) ∧
      ∃ (f : ∀ j, ι → Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel (U j) 0)
        (r : ∀ j, U j → ι → ℚ) (offset : V.analyticSpace → ι → ℂ),
        (∀ j i, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (f j i) = Intersection.CM.Construction.restrictSmoothForm (U j) 1 (a i).val) ∧
        ∀ j (x : U j) i, HolomorphicPrimitive.CM.Construction.zeroFormScalar (f j i) x = (r j x i : ℂ) + offset x.val i := by
  classical
  choose c hc b hb using fun i => RationalIntegrationDefect.CM.Construction.rational_integration_defect V (q i) (a i) (ha i)
  obtain ⟨s, U, W, hcontract, hcover, hWU, hcompact, f, hf⟩ := FiniteLocalPrimitives.CM.Construction.finite_primitive_cover a
  have hn (j : s) (i : ι) :
      ∃ (g : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel (U j) 0)
        (r : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of (U j))).X 0),
        Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d g = Intersection.CM.Construction.restrictSmoothForm (U j) 1 (a i).val ∧
        ∀ x : U j, HolomorphicPrimitive.CM.Construction.zeroFormScalar g x =
          ((AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) (TopCat.of (U j))).hom r x : ℂ) +
            ZeroCocycles.CM.Construction.smoothZeroCochainPoint V.analyticModel V.analyticSpace (b i) x.val := by
    let : ContractibleSpace (U j) := hcontract j
    exact LocalCochainNormalization.CM.Construction.normalized_local_rational_primitive (U j) Classical.ofNonempty
      (a i).val (c i) (b i) (hb i) (f j i) (hf j i)
  choose g r hg hr using hn
  exact ⟨s, U, W, hcover, hWU, hcompact, g,
    fun j x i => (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) (TopCat.of (U j))).hom (r j i) x,
    fun x i => ZeroCocycles.CM.Construction.smoothZeroCochainPoint V.analyticModel V.analyticSpace (b i) x,
    hg, fun j x i => hr j i x⟩

theorem exists_closed_representative_of_rational (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (q : V.rationalCohomology 1) :
    ∃ a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace 1,
      (V.deRhamBettiIso 1).hom (V.deRhamClass 1 a) = V.rationalCohomologyInclusion 1 q := by
  obtain ⟨a, ha⟩ := Analysis.DifferentialForms.Manifold.ClassRepresentatives.manifoldDeRhamFormClass_surjective V.analyticModel V.analyticSpace 1
    ((V.deRhamBettiIso 1).inv (V.rationalCohomologyInclusion 1 q))
  refine ⟨a, ?_⟩
  change (V.deRhamBettiIso 1).hom (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass V.analyticModel V.analyticSpace 1 a) = _
  rw [ha]
  exact (V.deRhamBettiIso 1).toLinearEquiv.apply_symm_apply _

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalPrimitiveCover.CM.Construction
