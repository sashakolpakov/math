import OAI.AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality
import OAI.AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexAugmentation
import OAI.AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains

/-! # Zero Cocycles -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ZeroCocycles.CM.Construction

noncomputable section

/-! Degree-zero cocycles are unchanged by the actual comparison from
ordinary singular cochains to smooth singular cochains. -/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff Simplicial

theorem cochainClass_zero_injective {R : Type} [Ring R]
    (K : CochainComplex (ModuleCat.{0} R) ℕ) :
    Function.Injective (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass K 0) := by
  intro a b hab
  obtain ⟨z, hz⟩ := (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists K 0 a b).mp hab
  have hf : (K.sc 0).f = 0 := by
    change K.d ((ComplexShape.up ℕ).prev 0) 0 = 0
    rw [CochainComplex.prev_nat_zero]
    exact K.shape 0 0 (by decide)
  rw [hf] at hz
  apply Subtype.ext
  exact sub_eq_zero.mp hz.symm

theorem quasiIso_zero_cocycle_surjective {R : Type} [Ring R]
    {K L : CochainComplex (ModuleCat.{0} R) ℕ} (f : K ⟶ L) [QuasiIso f] :
    Function.Surjective (AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap f 0) := by
  intro b
  obtain ⟨a, ha⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective K 0
    ((asIso (HomologicalComplex.homologyMap f 0)).inv (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass L 0 b))
  refine ⟨a, cochainClass_zero_injective L ?_⟩
  rw [← AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainClass_naturality, ha]
  exact (asIso (HomologicalComplex.homologyMap f 0)).inv_hom_id_apply _

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

def smoothPointSimplex (x : M) :
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet _⦋0⦌ :=
  ⟨TopCat.toSSetObj₀Equiv.symm x, AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.isManifoldSmoothSimplex_const E 0 x⟩

def smoothZeroCochainPoint (c : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).X 0)
    (x : M) : ℂ :=
  (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
    (ModuleCat.of ℂ ℂ) 0).hom c (smoothPointSimplex E M x)

theorem smoothZeroCochainPoint_add
    (a b : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).X 0) (x : M) :
    smoothZeroCochainPoint E M (a + b) x =
      smoothZeroCochainPoint E M a x + smoothZeroCochainPoint E M b x := by
  unfold smoothZeroCochainPoint
  rw [map_add]
  rfl

theorem smoothZeroCochainPoint_sub
    (a b : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).X 0) (x : M) :
    smoothZeroCochainPoint E M (a - b) x =
      smoothZeroCochainPoint E M a x - smoothZeroCochainPoint E M b x := by
  unfold smoothZeroCochainPoint
  rw [map_sub]
  rfl

theorem smoothZeroCochainPoint_restriction
    (c : (AlgebraicTopology.Cohomology.Singular.Basic.singularCochains (ModuleCat.of ℂ ℂ) (TopCat.of M)).X 0) (x : M) :
    smoothZeroCochainPoint E M
      ((AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M).f 0 c) x =
        (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCochainPointIso (ModuleCat.of ℂ ℂ) (TopCat.of M)).hom c x := by
  unfold smoothZeroCochainPoint
  change (AlgebraicTopology.Cohomology.Singular.Coefficients.degreewiseFunctionIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothSingularSubcomplex E M).toSSet
    (ModuleCat.of ℂ ℂ) 0).hom
      ((AlgebraicTopology.Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothInclusion E M)).f 0 c)
        (smoothPointSimplex E M x) = _
  rw [AlgebraicTopology.Cohomology.Singular.Formulas.degreewiseFunctionIso_pullback]
  rfl

variable [IsManifold 𝓘(ℝ, E) ∞ M]

theorem smoothZeroCochainPoint_integration (f : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 0) (x : M) :
    smoothZeroCochainPoint E M (AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain E M 0 f) x = f x 0 := by
  unfold smoothZeroCochainPoint
  rw [AlgebraicTopology.DeRham.Comparison.SmoothSimplexCochains.smoothSimplexCochain_function]
  exact AlgebraicTopology.DeRham.Comparison.SmoothSimplexAugmentation.smoothSimplexIntegration_zero (smoothPointSimplex E M x) f

theorem smooth_zero_cocycle_constant [PathConnectedSpace M]
    (c : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).X 0)
    (hc : (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M).d 0 1 c = 0)
    (x y : M) : smoothZeroCochainPoint E M c x = smoothZeroCochainPoint E M c y := by
  let : QuasiIso (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M) :=
    AlgebraicTopology.Cohomology.Singular.GlobalSmoothComparison.quasiIso_manifoldSmoothCochainRestriction E M
  let c' : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochains E (ModuleCat.of ℂ ℂ) M) 0 :=
    ⟨c, (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ 0 c).mpr hc⟩
  obtain ⟨b, hb⟩ := quasiIso_zero_cocycle_surjective
    (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M) c'
  have hval := congrArg Subtype.val hb
  change (AlgebraicTopology.Cohomology.Singular.ManifoldSmooth.manifoldSmoothCochainRestriction E (ModuleCat.of ℂ ℂ) M).f 0 b.val = c at hval
  rw [← hval, smoothZeroCochainPoint_restriction, smoothZeroCochainPoint_restriction]
  exact (AlgebraicTopology.Cohomology.Singular.Augmentation.singularZeroCoboundary_eq_zero_iff (ModuleCat.of ℂ ℂ) (TopCat.of M) b.val).mp
    ((AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ 0 b.val).mp b.property) x y (PathConnectedSpace.joined x y)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ZeroCocycles.CM.Construction
