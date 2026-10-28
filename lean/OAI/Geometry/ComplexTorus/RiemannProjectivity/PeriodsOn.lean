import OAI.AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.TraceForm
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-! # Periods On -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.PeriodsOn.Constructions.Periods

noncomputable section

/-!
# RiemannProjectivity: trace duality and the holomorphic period covectors

The trace identifies the rational vector space E with its rational dual.
After extension to ℂ, the prescribed positive embedding subspace pairs with
the period space by complex-linear covectors. This fixes the cohomological
sign convention in the realization construction. No singular-cohomology
comparison or algebraic realization is assumed in this file.
-/

open scoped _root_.NumberField TensorProduct Classical

variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]

/-- The rational trace pairing identifies E with its rational-linear dual. -/
def traceDualEquiv : E ≃ₗ[ℚ] Module.Dual ℚ E :=
  (Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)

@[simp]
theorem traceDualEquiv_apply (a b : E) :
    traceDualEquiv E a b = Algebra.trace ℚ E (a * b) := rfl

/-- Multiplication on E corresponds to pullback on the dual, as required
for the action on first cohomology rather than first homology. -/
theorem traceDualEquiv_multiplication (a x y : E) :
    traceDualEquiv E (a * x) y = traceDualEquiv E x (a * y) := by
  simp only [traceDualEquiv_apply]
  congr 1
  ring

/-- The scalar-extended trace pairing is diagonal in the embedding basis. -/
theorem traceForm_complex (x y : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E) :
    (Algebra.traceForm ℚ E).baseChange ℂ x y =
      ∑ σ : E →ₐ[ℚ] ℂ,
        AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E x σ * AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E y σ := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz =>
    simp only [map_add, LinearMap.add_apply, Pi.add_apply, hx, hz, add_mul,
      Finset.sum_add_distrib]
  | tmul a u =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz =>
      simp only [map_add, Pi.add_apply, hy, hz, mul_add, Finset.sum_add_distrib]
    | tmul b v =>
      rw [LinearMap.BilinForm.baseChange_tmul, Algebra.traceForm_apply]
      change algebraMap ℚ ℂ (Algebra.trace ℚ E (u * v)) * (a * b) = _
      rw [trace_eq_sum_embeddings ℂ]
      simp only [map_mul, AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv_tmul]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro σ _
      ring

/-- The complex-linear covector with the selected embedding coefficients. -/
def periodCovector (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E) :
    AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E →ₗ[ℂ] ℂ :=
  ∑ w : NumberField.InfinitePlace E,
    AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E x (Φ.placeEmbedding w) • LinearMap.proj w

theorem periodCovector_apply (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E) (z : AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) :
    periodCovector E Φ x z = ∑ w : NumberField.InfinitePlace E,
      AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E x (Φ.placeEmbedding w) * z w := by
  simp [periodCovector]

/-- A holomorphic vector has zero coordinates on the conjugate embeddings. -/
theorem holomorphic_conjugate_coordinate_zero
    (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E)
    (hx : x ∈ Φ.hodgeStructure.holomorphic) (w : NumberField.InfinitePlace E) :
    AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E x (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (Φ.placeEmbedding w)) = 0 := by
  by_contra hn
  have hs := (Φ.mem_subspace_iff true x).mp hx _ hn
  rw [Φ.property, Φ.placeEmbedding_positive] at hs
  exact Bool.noConfusion hs

/-- On the positive Hodge subspace, the trace functional is exactly the
complex-linear covector evaluated on the genuine period embedding. -/
theorem periodCovector_on_field
    (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E)
    (hx : x ∈ Φ.hodgeStructure.holomorphic) (a : E) :
    periodCovector E Φ x (Φ.periodEmbedding a) =
      (Algebra.traceForm ℚ E).baseChange ℂ x (1 ⊗ₜ[ℚ] a) := by
  rw [traceForm_complex, Φ.sum_embeddings_eq_sum_places]
  simp only [AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv_tmul, one_mul,
    holomorphic_conjugate_coordinate_zero E Φ x hx, zero_mul, add_zero]
  exact periodCovector_apply E Φ x (Φ.periodEmbedding a)

/-- Restriction to the positive Hodge subspace is a linear map into the
space of complex-linear covectors on the period space. -/
def holomorphicPeriodMap (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    Φ.hodgeStructure.holomorphic →ₗ[ℂ] Module.Dual ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) where
  toFun x := periodCovector E Φ x.val
  map_add' x y := by
    apply LinearMap.ext
    intro z
    simp only [periodCovector_apply, Submodule.coe_add, map_add,
      Pi.add_apply, add_mul, Finset.sum_add_distrib, LinearMap.add_apply]
  map_smul' a x := by
    apply LinearMap.ext
    intro z
    simp only [periodCovector_apply, Submodule.coe_smul, map_smul,
      Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum,
      LinearMap.smul_apply, RingHom.id_apply]

@[simp]
theorem periodCovector_single (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E)
    (x : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification E) (w : NumberField.InfinitePlace E) :
    periodCovector E Φ x (Pi.single w 1) =
      AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E x (Φ.placeEmbedding w) := by
  simp [periodCovector_apply, Pi.single_apply]

/-- All positive coordinates are recovered by evaluating on the coordinate
vectors; oddness determines the zero negative coordinates. -/
theorem holomorphicPeriodMap_injective (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    Function.Injective (holomorphicPeriodMap E Φ) := by
  intro x y hxy
  apply Subtype.ext
  apply (AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E).injective
  funext σ
  by_cases hσ : Φ.val σ = true
  · have h := congrArg
      (fun l : Module.Dual ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) =>
        l (Pi.single (NumberField.InfinitePlace.mk σ.toRingHom) 1)) hxy
    change periodCovector E Φ x.val _ = periodCovector E Φ y.val _ at h
    simpa only [periodCovector_single, Φ.placeEmbedding_mk σ hσ] using h
  · have hx : AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E x.val σ = 0 := by
      by_contra hn
      exact hσ ((Φ.mem_subspace_iff true x.val).mp x.property σ hn)
    have hy : AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E y.val σ = 0 := by
      by_contra hn
      exact hσ ((Φ.mem_subspace_iff true y.val).mp y.property σ hn)
    rw [hx, hy]

/-- Every period covector has an explicitly supported positive embedding
vector. Thus the identification is onto, not just a dimension bound. -/
theorem holomorphicPeriodMap_surjective (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    Function.Surjective (holomorphicPeriodMap E Φ) := by
  intro l
  let a : (E →ₐ[ℚ] ℂ) → ℂ := fun σ =>
    if Φ.val σ then l (Pi.single (NumberField.InfinitePlace.mk σ.toRingHom) 1) else 0
  let x := (AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E).symm a
  have hx : x ∈ Φ.hodgeStructure.holomorphic := by
    apply (Φ.mem_subspace_iff true x).mpr
    intro σ hn
    change AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E ((AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E).symm a) σ ≠ 0 at hn
    rw [LinearEquiv.apply_symm_apply] at hn
    by_contra hσ
    exact hn (by simp [a, hσ])
  refine ⟨⟨x, hx⟩, ?_⟩
  apply LinearMap.ext
  intro z
  change periodCovector E Φ x z = l z
  rw [periodCovector_apply]
  have ha (w : NumberField.InfinitePlace E) :
      AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E x (Φ.placeEmbedding w) = l (Pi.single w 1) := by
    simp only [x, LinearEquiv.apply_symm_apply, a, Φ.placeEmbedding_positive, ↓reduceIte]
    rw [Φ.mk_placeEmbedding]
  simp only [ha]
  have hz : z = ∑ w : NumberField.InfinitePlace E, z w • Pi.single w (1 : ℂ) := by
    ext w
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hz]
  simp [map_sum, map_smul, mul_comm]

/-- The prescribed holomorphic Hodge summand is exactly the dual of the
complex tangent model used to construct the period torus. -/
def holomorphicPeriodEquiv (Φ : AlgebraicGeometry.ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType E) :
    Φ.hodgeStructure.holomorphic ≃ₗ[ℂ] Module.Dual ℂ (AlgebraicGeometry.ComplexMultiplication.CM.PeriodSpace.CMPeriodSpace E) :=
  LinearEquiv.ofBijective (holomorphicPeriodMap E Φ)
    ⟨holomorphicPeriodMap_injective E Φ, holomorphicPeriodMap_surjective E Φ⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.PeriodsOn.Constructions.Periods
