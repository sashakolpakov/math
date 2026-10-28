import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolarizationFromRationalPairing
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Pairing

/-! # Polarization Factor -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PolarizationFactor.CM.Construction

noncomputable section

/-!
Retain the factorization through the vector-valued cup pairing when rational
approximation constructs a polarization. This supplies a construction in the
conclusion, not an assumption that an abstract polarization is geometric.
-/

open scoped TensorProduct BigOperators

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolarizationFromRationalPairing.CM.Construction

variable {U W : Type*} [AddCommGroup U] [Module ℚ U]
  [AddCommGroup W] [Module ℚ W] [FiniteDimensional ℚ W]

theorem exists_polarization_factoring
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U)
    (F : U →ₗ[ℚ] U →ₗ[ℚ] W) (hF : ∀ u, F u u = 0)
    (hiso : ∀ u ∈ H.holomorphic, ∀ v ∈ H.holomorphic,
      LinearMap.BilinMap.baseChange ℂ F u v = 0)
    (T : ComplexMultiplication.WeightOne.CM.Complexification W →ₗ[ℂ] ℂ)
    (hT : ∀ w : W, (T ((1 : ℂ) ⊗ₜ[ℚ] w)).im = 0)
    (hpos : ∀ u ∈ H.holomorphic, u ≠ 0 →
      0 < (Complex.I * T (LinearMap.BilinMap.baseChange ℂ F u
        (ComplexMultiplication.WeightOne.CM.coefficientConjugation U u))).re) :
    ∃ (P : ComplexMultiplication.CM.Polarization.WeightOnePolarization H) (trace : W →ₗ[ℚ] ℚ),
      P.form = F.compr₂ trace := by
  let b := Module.finBasis ℚ W
  have hB : ∀ i, (ComplexMultiplication.HodgeComparison.BilinearRational.CM.Construction.rationalBilinearCoordinate F b i).IsAlt := by
    intro i u
    change b.repr (F u u) i = 0
    rw [hF, map_zero, Finsupp.zero_apply]
  have hBi : ∀ i, ∀ u ∈ H.holomorphic, ∀ v ∈ H.holomorphic,
      (ComplexMultiplication.HodgeComparison.BilinearRational.CM.Construction.rationalBilinearCoordinate F b i).baseChange ℂ u v = 0 := by
    intro i u hu v hv
    rw [ComplexMultiplication.HodgeComparison.BilinearRational.CM.Construction.rationalBilinearCoordinate_baseChange, hiso u hu v hv, map_zero,
      Finsupp.zero_apply]
  have hBp : ∀ u ∈ H.holomorphic, u ≠ 0 →
      0 < (Complex.I * ∑ i, ((T ((1 : ℂ) ⊗ₜ[ℚ] b i)).re : ℂ) *
        (ComplexMultiplication.HodgeComparison.BilinearRational.CM.Construction.rationalBilinearCoordinate F b i).baseChange ℂ u
          (ComplexMultiplication.WeightOne.CM.coefficientConjugation U u)).re := by
    intro u hu hne
    rw [← ComplexMultiplication.HodgeComparison.BilinearRational.CM.Construction.rationalBilinear_real_functional_expansion F b T hT]
    exact hpos u hu hne
  obtain ⟨q, P, hP⟩ := ComplexMultiplication.HodgeComparison.RationalPolarizationApproximation.CM.Construction.exists_rational_polarization_of_real_combination H
    (ComplexMultiplication.HodgeComparison.BilinearRational.CM.Construction.rationalBilinearCoordinate F b) hB hBi
    (fun i => (T ((1 : ℂ) ⊗ₜ[ℚ] b i)).re) hBp
  refine ⟨P, ∑ i, q i • b.coord i, ?_⟩
  rw [hP]
  ext u v
  simp [ComplexMultiplication.HodgeComparison.BilinearRational.CM.Construction.rationalBilinearCoordinate, LinearMap.compr₂]

omit [FiniteDimensional ℚ W] in
/-- Factoring a bilinear form through a vector-valued pairing commutes
with the actual scalar-extension constructions. -/
theorem factored_form_baseChange
    (F : U →ₗ[ℚ] U →ₗ[ℚ] W) (trace : W →ₗ[ℚ] ℚ)
    (u v : ComplexMultiplication.WeightOne.CM.Complexification U) :
    LinearMap.BilinForm.baseChange ℂ (F.compr₂ trace) u v =
      ((Algebra.linearMap ℚ ℂ).comp trace).liftBaseChange ℂ
        (LinearMap.BilinMap.baseChange ℂ F u v) := by
  induction u using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | tmul a x =>
      induction v using TensorProduct.inductionOn with
      | add y z hy hz => simp only [map_add, hy, hz]
      | tmul b y => simp [LinearMap.BilinForm.baseChange_tmul,
          LinearMap.BilinMap.baseChange_tmul, LinearMap.compr₂, Algebra.smul_def, mul_comm]

/-- PolarizedPairing detects a nonzero vector-valued pairing once a polarization
has been constructed as a rational functional of that pairing. -/
theorem vector_pairing_ne_zero_of_polarization
    {E U W : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [AddCommGroup U] [Module ℚ U] [Module E U] [IsScalarTower ℚ E U]
    [AddCommGroup W] [Module ℚ W]
    (h_PolarizedPairing : Pairing.CM.Construction.PolarizedPairingInput) (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U)
    (P : ComplexMultiplication.CM.Polarization.WeightOnePolarization H) (hCM : ComplexMultiplication.WeightOne.CM.RankOneCMAction E H)
    (F : U →ₗ[ℚ] U →ₗ[ℚ] W) (trace : W →ₗ[ℚ] ℚ)
    (hP : P.form = F.compr₂ trace)
    (σ : E →ₐ[ℚ] ℂ) (u v : ComplexMultiplication.WeightOne.CM.Complexification U)
    (hu : u ∈ ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U σ)
    (hv : v ∈ ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ))
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    LinearMap.BilinMap.baseChange ℂ F u v ≠ 0 := by
  intro hz
  have hp := h_PolarizedPairing H P hCM σ u v hu hv hu0 hv0
  rw [hP, factored_form_baseChange, hz, map_zero] at hp
  exact hp rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PolarizationFactor.CM.Construction
