import OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dual.Basis

/-! # Duality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.Duality.CM

noncomputable section

/-!
# Universal coefficients with vector-valued coefficients

The actual evaluation map identifies cohomology with linear maps out of
homology over a field. Coefficients may be any vector space, including an
extension field of infinite degree. This is a step toward coefficient
extension for the CM theorem's actual singular cohomology.
-/

open _root_.CategoryTheory

variable {F : Type} [Field F]

/-- A vector-valued linear map vanishing on a kernel factors through the map.
The map on the image extends to the whole target by extending a basis. -/
theorem linearMapFactors_of_vanishesOnKernel
    {V W M : Type} [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    [AddCommGroup M] [Module F M]
    (f : V →ₗ[F] W) (φ : V →ₗ[F] M)
    (hφ : ∀ v : V, f v = 0 → φ v = 0) :
    ∃ ψ : W →ₗ[F] M, ψ.comp f = φ := by
  let q : V ⧸ LinearMap.ker f →ₗ[F] M :=
    (LinearMap.ker f).liftQ φ hφ
  let r : LinearMap.range f →ₗ[F] M := q.comp f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨ψ, hψ⟩ := r.exists_extend
  refine ⟨ψ, ?_⟩
  ext v
  have hv := LinearMap.congr_fun hψ (f.rangeRestrict v)
  change ψ (f v) = q (f.quotKerEquivRange.symm ⟨f v, _⟩) at hv
  rw [LinearMap.quotKerEquivRange_symm_apply_image] at hv
  exact hv

/-- A vector-valued cocycle which evaluates to zero on every cycle is a coboundary.
This uses the actual chain and cochain complexes in every degree, including zero. -/
theorem cochainClass_eq_zero_of_vanishesOnCycles_withCoefficients
    (K : SSet.{0}) (M : ModuleCat.{0} F) (n : ℕ)
    (c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains K M) n)
    (hc : ∀ z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := F) K) n,
      AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M n c.val z.val = 0) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains K M) n c = 0 := by
  let C := AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := F) K
  let D := AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains K M
  let φ : C.X n →ₗ[F] M := AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M n c.val
  obtain ⟨ψ, hψ⟩ := linearMapFactors_of_vanishesOnKernel (C.sc n).g.hom φ
    (fun z hz => hc ⟨z, hz⟩)
  let p : (D.sc n).X₁ :=
    (AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M ((ComplexShape.up ℕ).prev n)).symm ψ
  have hp : (D.sc n).f p = (c : D.X n) := by
    apply (AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M n).injective
    change AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M n
      (D.d ((ComplexShape.up ℕ).prev n) n p) = φ
    rw [AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_d]
    have he : AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M
        ((ComplexShape.up ℕ).prev n) p = ψ :=
      (AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M
        ((ComplexShape.up ℕ).prev n)).apply_symm_apply ψ
    rw [he]
    exact hψ
  apply (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_zero_iff D n c).mpr
  exact ⟨p, Subtype.ext hp⟩

/-- Every linear map on actual scalar homology is evaluation by a vector-valued cocycle.
The necessary extension from the cycle subspace is proved by mathlib's basis extension. -/
theorem exists_cocycle_realizing_homologyMap (K : SSet.{0}) (M : ModuleCat.{0} F) (n : ℕ)
    (L : (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := F) K).homology n →ₗ[F] M) :
    ∃ c : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains K M) n,
      ∀ z : AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainCycles (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := F) K) n,
        AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M n c.val z.val =
          L (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := F) K) n z) := by
  let C := AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := F) K
  let D := AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains K M
  obtain ⟨φ, hφ⟩ := (L.comp (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n)).exists_extend
  let c : D.X n := (AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M n).symm φ
  have hbound : φ.comp (C.sc n).f.hom = 0 := by
    ext z
    have hz := LinearMap.congr_fun hφ (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainBoundaryMap C n z)
    change φ ((C.sc n).f z) = L (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainBoundaryMap C n z)) at hz
    rw [AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_boundary, map_zero] at hz
    change φ ((C.sc n).f z) = 0
    exact hz
  have hc : c ∈ AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles D n := by
    change (D.d n ((ComplexShape.up ℕ).next n)) c = 0
    apply (AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M ((ComplexShape.up ℕ).next n)).injective
    rw [AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv_d, map_zero]
    have he : AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M n c = φ :=
      (AlgebraicTopology.Cohomology.Singular.ChainDual.degreewiseChainDualEquiv K M n).apply_symm_apply φ
    rw [he]
    exact hbound
  refine ⟨⟨c, hc⟩, fun z => ?_⟩
  have hz := LinearMap.congr_fun hφ z
  simpa only [c, LinearEquiv.apply_symm_apply, LinearMap.comp_apply,
    Submodule.subtype_apply] using hz

/-- Over a field, two cohomology classes are equal whenever their canonical
evaluations on all homology classes agree. -/
theorem simplicialEvaluationWithCoefficients_injective (K : SSet.{0}) (M : ModuleCat.{0} F) (n : ℕ) :
    Function.Injective (AlgebraicTopology.Cohomology.Singular.Evaluation.simplicialHomologyEvaluation K M n) := by
  intro a b hab
  let C := AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := F) K
  let D := AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains K M
  have hzero : AlgebraicTopology.Cohomology.Singular.Evaluation.simplicialHomologyEvaluation K M n (a - b) = 0 := by
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_surjective D n (a - b)
  have hc0 : AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass D n c = 0 := by
    apply cochainClass_eq_zero_of_vanishesOnCycles_withCoefficients K M n c
    intro z
    have hz : AlgebraicTopology.Cohomology.Singular.Evaluation.simplicialHomologyEvaluation K M n
        (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass D n c) (AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass C n z) = 0 := by
      rw [hc, hzero]
      rfl
    exact (AlgebraicTopology.Cohomology.Singular.Evaluation.simplicialHomologyEvaluation_class_class K M n c z).symm.trans hz
  exact sub_eq_zero.mp (hc.symm.trans hc0)

/-- Every linear map on homology is canonical evaluation by a
cohomology class when the coefficient ring is a field. -/
theorem simplicialEvaluationWithCoefficients_surjective (K : SSet.{0}) (M : ModuleCat.{0} F) (n : ℕ) :
    Function.Surjective (AlgebraicTopology.Cohomology.Singular.Evaluation.simplicialHomologyEvaluation K M n) := by
  intro L
  obtain ⟨c, hc⟩ := exists_cocycle_realizing_homologyMap K M n L
  refine ⟨AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains K M) n c, ?_⟩
  ext h
  obtain ⟨z, rfl⟩ := AlgebraicTopology.Cohomology.Singular.ChainRepresentatives.chainClass_surjective (AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := F) K) n h
  rw [AlgebraicTopology.Cohomology.Singular.Evaluation.simplicialHomologyEvaluation_class_class]
  exact hc z

/-- Universal-coefficient duality with arbitrary vector-space coefficients. -/
def simplicialEvaluationWithCoefficientsEquiv (K : SSet.{0})
    (M : ModuleCat.{0} F) (n : ℕ) :
    (AlgebraicTopology.Cohomology.Singular.Basic.simplicialCochains K M).homology n ≃ₗ[F]
      ((AlgebraicTopology.Cohomology.Singular.ChainDual.simplicialScalarChains (R := F) K).homology n →ₗ[F] M) :=
  LinearEquiv.ofBijective (AlgebraicTopology.Cohomology.Singular.Evaluation.simplicialHomologyEvaluation K M n)
    ⟨simplicialEvaluationWithCoefficients_injective K M n,
      simplicialEvaluationWithCoefficients_surjective K M n⟩

/-- The forward map is the existing evaluation on genuine singular chains. -/
def singularEvaluationWithCoefficientsEquiv (M : ModuleCat.{0} F)
    (X : TopCat.{0}) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology M X n ≃ₗ[F]
      ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := F) X).homology n →ₗ[F] M) :=
  simplicialEvaluationWithCoefficientsEquiv (TopCat.toSSet.obj X) M n

@[simp]
theorem singularEvaluationWithCoefficientsEquiv_apply (M : ModuleCat.{0} F)
    (X : TopCat.{0}) (n : ℕ) (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology M X n) :
    singularEvaluationWithCoefficientsEquiv M X n c =
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation M X n c := rfl

/-- Finite-dimensional scalar cohomology forces finite-dimensional homology.
This follows from actual evaluation duality, without a finite-chain model. -/
theorem finite_homology_of_finite_cohomology (X : TopCat.{0}) (n : ℕ)
    [Module.Finite F (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of F F) X n)] :
    Module.Finite F ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := F) X).homology n) := by
  let : Module.Finite F (Module.Dual F
      ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := F) X).homology n)) :=
    Module.Finite.of_surjective (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X n).toLinearMap
      (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X n).surjective
  exact (Module.finite_dual_iff F).mp inferInstance

/-- A finite homology basis expands every class with arbitrary vector-valued
coefficients as a sum of actual changes of coefficients of scalar classes. -/
theorem coefficient_expansion_in_homology_basis (M : ModuleCat.{0} F)
    (X : TopCat.{0}) (n : ℕ) {ι : Type} [Fintype ι]
    (b : Module.Basis ι F ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := F) X).homology n))
    (c : AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology M X n) :
    c = ∑ i, AlgebraicTopology.Cohomology.Singular.Coefficients.coefficientMap
      (ModuleCat.ofHom (LinearMap.toSpanSingleton F M
        (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation M X n c (b i)))) X n
      ((AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X n).symm (b.coord i)) := by
  apply (singularEvaluationWithCoefficientsEquiv M X n).injective
  ext z
  change AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation M X n c z = _
  simp only [map_sum, singularEvaluationWithCoefficientsEquiv_apply,
    LinearMap.sum_apply, AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_coefficient]
  have he (i : ι) : AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of F F) X n
      ((AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X n).symm (b.coord i)) = b.coord i :=
    (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv X n).apply_symm_apply (b.coord i)
  simp only [he]
  change AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation M X n c z =
    ∑ i, b.coord i z • AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation M X n c (b i)
  have hz := congrArg (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation M X n c) (b.sum_repr z)
  simpa only [map_sum, map_smul, Module.Basis.coord_apply] using hz.symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.Coefficient.Duality.CM
