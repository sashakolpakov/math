import OAI.RepresentationTheory.Weil.UnitarySplitting.TracePairing
import OAI.RepresentationTheory.Weil.UnitarySplitting.Characters

/-! # Quadratic Norm -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticNorm.Construction

noncomputable section

section

/-! Explicit trace and norm formulas for the specified quadratic involution,
and the norm invariance of the permitted splitting characters. -/

open scoped BigOperators

section Field

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable [FiniteDimensional F E] [CharZero F]
variable (hQuadratic : Module.finrank F E = 2) (σ : E ≃ₐ[F] E)
variable (hne : ∃ z : E, σ z ≠ z)

local instance : DecidableEq (E ≃ₐ[F] E) := Classical.decEq _

include hQuadratic hne in
theorem quadratic_automorphisms : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, σ} := by
  classical
  let : Algebra.IsQuadraticExtension F E := ⟨hQuadratic⟩
  have hσ : (1 : E ≃ₐ[F] E) ≠ σ := by
    intro hh
    obtain ⟨z, hz⟩ := hne
    rw [← hh] at hz
    exact hz rfl
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hQuadratic]
  apply Eq.symm
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simp only [Finset.card_univ, hcard, Finset.card_pair hσ, le_refl]

include hQuadratic hne in
theorem quadratic_norm_formula (x : E) :
    algebraMap F E (Algebra.norm F x) = x * σ x := by
  classical
  let : Algebra.IsQuadraticExtension F E := ⟨hQuadratic⟩
  rw [Algebra.norm_eq_prod_automorphisms, quadratic_automorphisms hQuadratic σ hne]
  have hσ : (1 : E ≃ₐ[F] E) ≠ σ := by
    intro hh
    obtain ⟨z, hz⟩ := hne
    rw [← hh] at hz
    exact hz rfl
  simp only [Finset.prod_pair hσ, AlgEquiv.one_apply]

include hQuadratic hne in
theorem quadratic_trace_formula (x : E) :
    algebraMap F E (Algebra.trace F E x) = x + σ x := by
  classical
  let : Algebra.IsQuadraticExtension F E := ⟨hQuadratic⟩
  rw [trace_eq_sum_automorphisms, quadratic_automorphisms hQuadratic σ hne]
  have hσ : (1 : E ≃ₐ[F] E) ≠ σ := by
    intro hh
    obtain ⟨z, hz⟩ := hne
    rw [← hh] at hz
    exact hz rfl
  simp only [Finset.sum_pair hσ, AlgEquiv.one_apply]

include hQuadratic hne in
theorem quadratic_fixed_iff (x : E) : σ x = x ↔ x ∈ Set.range (algebraMap F E) := by
  classical
  let : Algebra.IsQuadraticExtension F E := ⟨hQuadratic⟩
  rw [IsGalois.mem_range_algebraMap_iff_fixed]
  constructor
  · intro hx τ
    have ht : τ ∈ ({1, σ} : Finset (E ≃ₐ[F] E)) := by
      rw [← quadratic_automorphisms hQuadratic σ hne]
      exact Finset.mem_univ τ
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · rfl
    · exact hx
  · exact fun h => h σ

end Field

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [FiniteDimensional F E]
variable (ω : Fˣ →ₜ* Circle) (hω : UnitarySplitting.Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
variable {d : ℕ} (χ : Eˣ →ₜ* Circle) (hχ : UnitarySplitting.Characters.Construction.HasSplittingRestriction ω d χ)

include hω hχ in
omit [FiniteDimensional F E] in
theorem splittingCharacter_norm (b : Eˣ) :
    χ (Units.map (algebraMap F E).toMonoidHom (Units.map (Algebra.norm F) b)) = 1 := by
  rw [hχ]
  have hh : ω (Units.map (Algebra.norm F) b) = 1 :=
    (hω _).mpr ⟨b, rfl⟩
  rw [hh, one_pow]

include hω hχ in
theorem splittingCharacter_conjugate [CharZero F]
    (hQuadratic : Module.finrank F E = 2) (σ : E ≃ₐ[F] E)
    (hne : ∃ z : E, σ z ≠ z) (b : Eˣ) :
    χ (Units.map σ.toMonoidHom b) * χ b = 1 := by
  rw [← map_mul]
  have he : Units.map σ.toMonoidHom b * b =
      Units.map (algebraMap F E).toMonoidHom (Units.map (Algebra.norm F) b) := by
    apply Units.ext
    change σ (b : E) * (b : E) = algebraMap F E (Algebra.norm F (b : E))
    rw [quadratic_norm_formula hQuadratic σ hne, mul_comm]
  rw [he]
  exact splittingCharacter_norm ω hω χ hχ b

end

/-! Topological field coordinates and continuity of the quadratic norm.
Only continuity of the given field embedding is assumed. -/

open _root_.Topology

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [CompleteSpace F]
variable (hF : ¬ DiscreteTopology F) (hEmbedding : Continuous (algebraMap F E))

include hF hEmbedding in
theorem fieldEmbedding_isClosedEmbedding : IsClosedEmbedding (algebraMap F E) := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField F with hd | ⟨_, rfl⟩
  · exact (hF hd).elim
  · let : ContinuousSMul F E := continuousSMul_of_algebraMap F E hEmbedding
    exact LinearMap.isClosedEmbedding_of_injective
      (f := (Algebra.ofId F E).toLinearMap)
      (LinearMap.ker_eq_bot.mpr (algebraMap F E).injective)

variable [FiniteDimensional F E]

include hF hEmbedding in
theorem fieldAutomorphism_continuous (σ : E ≃ₐ[F] E) : Continuous σ := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField F with hd | ⟨_, rfl⟩
  · exact (hF hd).elim
  · let : ContinuousSMul F E := continuousSMul_of_algebraMap F E hEmbedding
    exact σ.toLinearMap.continuous_of_finiteDimensional

include hF hEmbedding in
theorem fieldTrace_continuous : Continuous (Algebra.trace F E) := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField F with hd | ⟨_, rfl⟩
  · exact (hF hd).elim
  · let : ContinuousSMul F E := continuousSMul_of_algebraMap F E hEmbedding
    exact (Algebra.trace F E).continuous_of_finiteDimensional

include hF hEmbedding in
theorem fieldNorm_continuous : Continuous (Algebra.norm F : E → F) := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField F with hd | ⟨_, rfl⟩
  · exact (hF hd).elim
  · let : ContinuousSMul F E := continuousSMul_of_algebraMap F E hEmbedding
    let b := Module.finBasis F E
    have hc := continuous_id.matrix_det.comp (Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional
    convert hc using 1
    funext x
    exact Algebra.norm_eq_matrix_det b x

def quadraticFieldCoordinates (hQuadratic : Module.finrank F E = 2) : E ≃L[F] (Fin 2 → F) := by
  apply Classical.choice
  rcases NormedField.discreteTopology_or_nontriviallyNormedField F with hd | ⟨_, rfl⟩
  · exact (hF hd).elim
  · let : ContinuousSMul F E := continuousSMul_of_algebraMap F E hEmbedding
    let b := (Module.finBasis F E).reindex (finCongr hQuadratic)
    exact ⟨b.equivFun.toContinuousLinearEquiv⟩

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticNorm.Construction
