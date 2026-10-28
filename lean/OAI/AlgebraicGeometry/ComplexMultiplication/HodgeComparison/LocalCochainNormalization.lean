import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NormalizedPrimitives
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalSmoothCochains
import OAI.AlgebraicTopology.Cohomology.Singular.Contractible

/-! # Local Cochain Normalization -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalCochainNormalization.CM.Construction

noncomputable section

/-! Normalize local differential-form primitives using actual rational
singular primitives and the global integration coboundary. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.Contractible
open scoped _root_.Manifold ContDiff

theorem cochain_add_primitive_of_defect {R : Type} [Ring R]
    {K L : CochainComplex (ModuleCat.{0} R) ℕ} (f : K ⟶ L)
    (a c : K.X 1) (b : K.X 0) (hb : K.d 0 1 b = a - c)
    (q : L.X 0) (hq : L.d 0 1 q = f.f 1 c) :
    L.d 0 1 (q + f.f 0 b) = f.f 1 a := by
  have h := ConcreteCategory.congr_hom (f.comm 0 1) b
  change L.d 0 1 (f.f 0 b) = f.f 1 (K.d 0 1 b) at h
  rw [map_add, hq, h, hb, map_sub]
  abel

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {F N : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace N] [ChartedSpace F N]

theorem smoothZeroCochainPoint_pullback (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f)
    (b : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains F (ModuleCat.of ℂ ℂ) N).X 0) (x : M) :
    ZeroCocycles.CM.Construction.smoothZeroCochainPoint E M
      ((AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback E F (ModuleCat.of ℂ ℂ) f hf).f 0 b) x =
      ZeroCocycles.CM.Construction.smoothZeroCochainPoint F N b (f x) := by
  unfold ZeroCocycles.CM.Construction.smoothZeroCochainPoint
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
    (ModuleCat.of ℂ ℂ) 0).hom
      ((AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) (AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothSingularMap E F f hf)).f 0 b)
        (ZeroCocycles.CM.Construction.smoothPointSimplex E M x) = _
  rw [AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback]
  rfl

variable [IsManifold 𝓘(ℝ, E) ∞ M]

theorem normalized_local_rational_primitive (U : Opens M) [ContractibleSpace U]
    (x₀ : U) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 1)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.singularCocycles (ModuleCat.of ℚ ℚ) (TopCat.of M) 1)
    (b : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).X 0)
    (hb : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).d 0 1 b =
      AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M 1 a - RationalSmoothCochains.CM.Construction.rationalSmoothCochain E M 1 c.val)
    (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U 0)
    (hf : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f = Intersection.CM.Construction.restrictSmoothForm U 1 a) :
    ∃ (g : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E U 0)
      (q : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℚ ℚ) (TopCat.of U)).X 0),
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d g = Intersection.CM.Construction.restrictSmoothForm U 1 a ∧
      ∀ x : U, HolomorphicPrimitive.CM.Construction.zeroFormScalar g x =
        ((AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℚ ℚ) (TopCat.of U)).hom q x : ℂ) +
          ZeroCocycles.CM.Construction.smoothZeroCochainPoint E M b x.val := by
  let i : U → M := Subtype.val
  have hi : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ i := contMDiff_subtype_val
  let p := AlgebraicTopology.Cohomology.Singular.ManifoldSmoothFunctor.manifoldSmoothPullback E E (ModuleCat.of ℂ ℂ) i hi
  let cu := AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.singularCocyclePullback (ModuleCat.of ℚ ℚ) (TopCat.ofHom ⟨i, hi.continuous⟩) 1 c
  obtain ⟨q, hq⟩ := AlgebraicTopology.Cohomology.Singular.Contractible.exists_singularPrimitive_of_contractible
    (ModuleCat.of ℚ ℚ) (TopCat.of U) 0 cu
  let qc := RationalSmoothCochains.CM.Construction.rationalSmoothCochain E U 0 q
  have hqc : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) U).d 0 1 qc =
      p.f 1 (RationalSmoothCochains.CM.Construction.rationalSmoothCochain E M 1 c.val) := by
    change (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) U).d 0 1
      (RationalSmoothCochains.CM.Construction.rationalSmoothCochain E U 0 q) = _
    rw [RationalSmoothCochains.CM.Construction.rationalSmoothCochain_d, hq]
    exact (RationalSmoothCochains.CM.Construction.rationalSmoothCochain_pullback i hi 1 c.val).symm
  have hd := cochain_add_primitive_of_defect p
    (AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M 1 a) (RationalSmoothCochains.CM.Construction.rationalSmoothCochain E M 1 c.val) b hb qc hqc
  have hiForm := ConcreteCategory.congr_hom (AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain_naturality i hi 1) a
  have hnormal : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) U).d 0 1 (qc + p.f 0 b) =
      AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E U 1 (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d f) := by
    rw [hf]
    exact hd.trans hiForm.symm
  obtain ⟨g, hg, hscalar⟩ := NormalizedPrimitives.CM.Construction.normalize_primitive_against_zero_cochain E U x₀ f
    (qc + p.f 0 b) hnormal
  refine ⟨g, q, hg.trans hf, ?_⟩
  intro x
  exact (hscalar x).trans ((ZeroCocycles.CM.Construction.smoothZeroCochainPoint_add E U qc (p.f 0 b) x).trans
    (congrArg₂ (· + ·) (RationalSmoothCochains.CM.Construction.rationalSmoothCochain_point E U q x)
      (smoothZeroCochainPoint_pullback i hi b x)))

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalCochainNormalization.CM.Construction
