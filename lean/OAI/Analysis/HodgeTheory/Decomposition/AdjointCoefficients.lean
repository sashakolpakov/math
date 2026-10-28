import OAI.Analysis.HodgeTheory.Decomposition.CoordinateMetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! # Adjoint Coefficients -/

namespace OAI.Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions

noncomputable section

section

/-! Smooth local formal-adjoint coefficients for the genuine projective form
metric, including its positive volume density. -/

open scoped ContDiff _root_.Manifold

section Inversion

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem positiveOperator_isInvertible (A : F →L[ℝ] F)
    (hpos : ∀ u : F, u ≠ 0 → 0 < inner ℝ (A u) u) : A.IsInvertible := by
  have hzero (u : F) (hu : A u = 0) : u = 0 := by
    by_contra hn
    have hp := hpos u hn
    rw [hu, inner_zero_left] at hp
    exact (lt_irrefl 0) hp
  have hi : Function.Injective A := by
    intro u v huv
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, huv, sub_self]
  let e := (LinearEquiv.ofBijective A.toLinearMap
    ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩).toContinuousLinearEquiv
  refine ⟨e, ?_⟩
  ext u
  rfl

theorem inverseOperator_smoothOn {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    (A : D → F →L[ℝ] F) {U : Set D} (hU : IsOpen U) (hA : ContDiffOn ℝ ∞ A U)
    (hinv : ∀ y ∈ U, (A y).IsInvertible) :
    ContDiffOn ℝ ∞ (fun y => (A y).inverse) U := by
  intro y hy
  exact ((hinv y hy).contDiffAt_map_inverse.comp y
    (hA.contDiffAt (hU.mem_nhds hy))).contDiffWithinAt

end Inversion

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

abbrev ProjectiveRealCoordinateIndex := Fin (Module.finrank ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))

/-- The fixed analytic-coordinate real basis transported from Euclidean coordinates. -/
def projectiveReferenceBasis : Module.Basis (ProjectiveRealCoordinateIndex V) ℝ V.analyticModel :=
  (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis.map
    ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).toLinearEquiv.restrictScalars ℝ)

def projectiveEuclideanExteriorSymbol (n : ℕ) (i : ProjectiveRealCoordinateIndex V) :
    SymbolDifferential.Constructions.ExteriorCoordinates (ProjectiveRealCoordinateIndex V) n →L[ℝ]
      SymbolDifferential.Constructions.ExteriorCoordinates (ProjectiveRealCoordinateIndex V) (n + 1) :=
  SymbolDifferential.Constructions.coordinateExteriorSymbol (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n i

variable (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

/-- The actual form metric times its actual volume density, in Euclidean chart coordinates. -/
def projectiveWeightedFormOperator (n : ℕ) (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    SymbolDifferential.Constructions.ExteriorCoordinates (ProjectiveRealCoordinateIndex V) n →L[ℝ]
      SymbolDifferential.Constructions.ExteriorCoordinates (ProjectiveRealCoordinateIndex V) n :=
  AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z •
    CoordinateMetric.Constructions.projectiveCoordinateMetricOperator V e (projectiveReferenceBasis V) n (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)

include he

theorem projectiveWeightedFormOperator_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (projectiveWeightedFormOperator V e n) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) := by
  have hM := (CoordinateMetric.Constructions.projectiveCoordinateMetric_smooth V e he (projectiveReferenceBasis V) n).comp
    ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).contDiff.restrict_scalars ℝ).contDiffOn
    (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates_mapsTo V e)
  exact (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_smooth V e he).smul hM

theorem projectiveWeightedFormOperator_positive (n : ℕ) (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u : SymbolDifferential.Constructions.ExteriorCoordinates (ProjectiveRealCoordinateIndex V) n)
    (hu : u ≠ 0) : 0 < inner ℝ (projectiveWeightedFormOperator V e n z u) u := by
  change 0 < inner ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z •
    (CoordinateMetric.Constructions.projectiveCoordinateMetricOperator V e (projectiveReferenceBasis V) n (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) u)) u
  rw [real_inner_smul_left]
  exact mul_pos (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_pos V e he hz)
    (CoordinateMetric.Constructions.projectiveCoordinateMetric_positive V e he (projectiveReferenceBasis V) n
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz u hu)

theorem projectiveWeightedFormOperator_symmetric (n : ℕ) (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) (u v : SymbolDifferential.Constructions.ExteriorCoordinates (ProjectiveRealCoordinateIndex V) n) :
    inner ℝ (projectiveWeightedFormOperator V e n z u) v =
      inner ℝ (projectiveWeightedFormOperator V e n z v) u := by
  simp only [projectiveWeightedFormOperator, smul_apply, real_inner_smul_left]
  rw [CoordinateMetric.Constructions.projectiveCoordinateMetric_symmetric V e he (projectiveReferenceBasis V) n (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z) hz]

theorem projectiveWeightedFormOperator_isInvertible (n : ℕ) (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) : (projectiveWeightedFormOperator V e n z).IsInvertible :=
  positiveOperator_isInvertible _ (projectiveWeightedFormOperator_positive V e he n z hz)

theorem projectiveWeightedFormOperator_inverse_smooth (n : ℕ) :
    ContDiffOn ℝ ∞ (fun z => (projectiveWeightedFormOperator V e n z).inverse)
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) :=
  inverseOperator_smoothOn _ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
    (projectiveWeightedFormOperator_smooth V e he n) (projectiveWeightedFormOperator_isInvertible V e he n)

/-- The explicit local formula for the formal adjoint, including both degree metrics. -/
def projectiveLocalAdjointCoefficients (n : ℕ)
    (v : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → SymbolDifferential.Constructions.ExteriorCoordinates (ProjectiveRealCoordinateIndex V) (n + 1))
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) : SymbolDifferential.Constructions.ExteriorCoordinates (ProjectiveRealCoordinateIndex V) n :=
  (projectiveWeightedFormOperator V e n z).inverse
    (LocalAdjoint.Constructions.formalAdjointNumerator (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
      (projectiveEuclideanExteriorSymbol V n) (projectiveWeightedFormOperator V e (n + 1)) v z)

theorem projectiveLocalAdjointCoefficients_smooth (n : ℕ)
    (v : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → SymbolDifferential.Constructions.ExteriorCoordinates (ProjectiveRealCoordinateIndex V) (n + 1))
    (hv : ContDiffOn ℝ ∞ v (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _)) :
    ContDiffOn ℝ ∞ (projectiveLocalAdjointCoefficients V e n v) (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _) :=
  (projectiveWeightedFormOperator_inverse_smooth V e he n).clm_apply
    (LocalAdjoint.Constructions.formalAdjointNumerator_smoothOn _ _ _ v (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen
      (projectiveWeightedFormOperator_smooth V e he (n + 1)) hv)

end

/-! First-order and order-zero parts of the actual local formal adjoint. -/

open scoped ContDiff BigOperators

section General

variable {E F G ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

theorem formalAdjointNumerator_expansion (directions : ι → E) (symbol : ι → F →L[ℝ] G)
    (weight : E → G →L[ℝ] G) (v : E → G) (x : E)
    (hweight : DifferentiableAt ℝ weight x) (hv : DifferentiableAt ℝ v x) :
    LocalAdjoint.Constructions.formalAdjointNumerator directions symbol weight v x =
      -∑ i, (symbol i).adjoint
        (weight x (fderiv ℝ v x (directions i)) + (fderiv ℝ weight x (directions i)) (v x)) := by
  unfold LocalAdjoint.Constructions.formalAdjointNumerator
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have h := ((symbol i).adjoint.hasFDerivAt.comp x
    (hweight.hasFDerivAt.clm_apply hv.hasFDerivAt)).fderiv
  exact congrArg (fun L : E →L[ℝ] F => L (directions i)) h

end General

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

include he

/-- The principal derivative part and the differentiated-metric remainder are explicit. -/
theorem projectiveLocalAdjointCoefficients_expansion
    (v : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V → SymbolDifferential.Constructions.ExteriorCoordinates (ProjectiveRealCoordinateIndex V) (n + 1))
    (hv : ContDiffOn ℝ ∞ v (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e : Set _))
    (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    let directions := stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    let S := projectiveEuclideanExteriorSymbol V n
    let A := projectiveWeightedFormOperator V e n z
    let B := projectiveWeightedFormOperator V e (n + 1)
    projectiveLocalAdjointCoefficients V e n v z =
      -(∑ i, A.inverse ((S i).adjoint (B z (fderiv ℝ v z (directions i))))) -
        ∑ i, A.inverse ((S i).adjoint ((fderiv ℝ B z (directions i)) (v z))) := by
  dsimp only
  have hB := ((projectiveWeightedFormOperator_smooth V e he (n + 1)).contDiffAt
    ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  have hv' := (hv.contDiffAt ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e).isOpen.mem_nhds hz)).differentiableAt (by simp)
  rw [projectiveLocalAdjointCoefficients, formalAdjointNumerator_expansion _ _ _ v z hB hv']
  simp only [map_neg, map_sum, map_add, Finset.sum_add_distrib]
  abel

end

end OAI.Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions
