import OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition
import OAI.AlgebraicGeometry.ComplexMultiplication.SignSwitch
import Mathlib.LinearAlgebra.Projection

/-! # Embedding Hodge Type -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication

noncomputable section

/-!
# Hodge types of the actual CM embedding lines

Each one-dimensional embedding space is entirely holomorphic or entirely
antiholomorphic. The proof uses invariance of the Hodge summands under the
field action and the associated projections. Coefficient conjugation swaps
the two types and conjugates the embedding, giving the manuscript's odd sign
functions on the actual embedding lines.
-/

open scoped TensorProduct Classical

/-- Conjugation of an embedding acts on its complex values. -/
def EmbeddingHodgeType.CM.conjugateEmbedding {E : Type*} [Field E] [Algebra ℚ E]
    (σ : E →ₐ[ℚ] ℂ) : E →ₐ[ℚ] ℂ :=
  (Complex.conjAe.restrictScalars ℚ).toAlgHom.comp σ

@[simp]
theorem EmbeddingHodgeType.CM.conjugateEmbedding_apply {E : Type*} [Field E] [Algebra ℚ E]
    (σ : E →ₐ[ℚ] ℂ) (a : E) : EmbeddingHodgeType.CM.conjugateEmbedding σ a = star (σ a) := rfl

@[simp]
theorem EmbeddingHodgeType.CM.conjugateEmbedding_involutive {E : Type*} [Field E] [Algebra ℚ E]
    (σ : E →ₐ[ℚ] ℂ) : EmbeddingHodgeType.CM.conjugateEmbedding (EmbeddingHodgeType.CM.conjugateEmbedding σ) = σ := by
  ext a
  simp

/-- Coefficient conjugation is semilinear for the ordinary complex action. -/
theorem EmbeddingHodgeType.CM.coefficientConjugation_smul (U : Type*) [AddCommGroup U] [Module ℚ U]
    (z : ℂ) (x : WeightOne.CM.Complexification U) :
    WeightOne.CM.coefficientConjugation U (z • x) = star z • WeightOne.CM.coefficientConjugation U x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul a u => simp [TensorProduct.smul_tmul']

/-- A linear map preserving two complementary subspaces commutes with their
projection. This is the linear-algebra step needed to split eigenvectors by type. -/
theorem EmbeddingHodgeType.CM.projection_commutes_of_preserves {K V : Type*} [Field K]
    [AddCommGroup V] [Module K V] {p q : Submodule K V} (hpq : IsCompl p q)
    (f : V →ₗ[K] V) (hp : ∀ x ∈ p, f x ∈ p) (hq : ∀ x ∈ q, f x ∈ q) (x : V) :
    p.projection q hpq (f x) = f (p.projection q hpq x) := by
  obtain ⟨u, v, huv, _⟩ := Submodule.existsUnique_add_of_isCompl hpq x
  rw [← huv, map_add, map_add, map_add]
  rw [Submodule.projection_apply_of_mem_left hpq (hp u u.property),
    Submodule.projection_apply_of_mem_right hpq (hq v v.property),
    Submodule.projection_apply_left, Submodule.projection_apply_right]
  simp only [add_zero]

section EmbeddingSpaces

variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]
variable (U : Type*) [AddCommGroup U] [Module ℚ U] [Module E U] [IsScalarTower ℚ E U]

omit [NumberField E] [IsScalarTower ℚ E U] in
/-- Actual coefficient conjugation sends each eigenspace to its conjugate. -/
theorem EmbeddingHodgeType.CM.coefficientConjugation_mem_embeddingSpace (σ : E →ₐ[ℚ] ℂ)
    {x : WeightOne.CM.Complexification U} (hx : x ∈ EmbeddingDecomposition.CM.embeddingSpace E U σ) :
    WeightOne.CM.coefficientConjugation U x ∈ EmbeddingDecomposition.CM.embeddingSpace E U (EmbeddingHodgeType.CM.conjugateEmbedding σ) := by
  apply (EmbeddingDecomposition.CM.mem_embeddingSpace E U _ _).mpr
  intro a
  rw [WeightOne.CM.baseChange_coefficientConjugation,
    (EmbeddingDecomposition.CM.mem_embeddingSpace E U σ x).mp hx a, EmbeddingHodgeType.CM.coefficientConjugation_smul]
  rfl

omit [NumberField E] [IsScalarTower ℚ E U] in
/-- Conjugation is a bijection between the two embedding spaces. -/
theorem EmbeddingHodgeType.CM.coefficientConjugation_mem_embeddingSpace_iff (σ : E →ₐ[ℚ] ℂ)
    (x : WeightOne.CM.Complexification U) :
    WeightOne.CM.coefficientConjugation U x ∈ EmbeddingDecomposition.CM.embeddingSpace E U (EmbeddingHodgeType.CM.conjugateEmbedding σ) ↔
      x ∈ EmbeddingDecomposition.CM.embeddingSpace E U σ := by
  constructor
  · intro hx
    simpa using EmbeddingHodgeType.CM.coefficientConjugation_mem_embeddingSpace E U (EmbeddingHodgeType.CM.conjugateEmbedding σ) hx
  · exact EmbeddingHodgeType.CM.coefficientConjugation_mem_embeddingSpace E U σ

end EmbeddingSpaces

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E]
variable {U : Type*} [AddCommGroup U] [Module ℚ U] [Module E U] [IsScalarTower ℚ E U]
variable {H : WeightOne.CM.WeightOneHodgeStructure U} (h : WeightOne.CM.RankOneCMAction E H)

include h in
omit [NumberField E] [IsScalarTower ℚ E U] in
/-- Projecting an eigenvector onto its holomorphic part preserves its field
character, because the field acts by Hodge endomorphisms. -/
theorem WeightOne.CM.RankOneCMAction.holomorphicProjection_mem_embeddingSpace (σ : E →ₐ[ℚ] ℂ)
    {x : WeightOne.CM.Complexification U} (hx : x ∈ EmbeddingDecomposition.CM.embeddingSpace E U σ) :
    H.holomorphic.projection H.antiholomorphic H.complementary x ∈ EmbeddingDecomposition.CM.embeddingSpace E U σ := by
  apply (EmbeddingDecomposition.CM.mem_embeddingSpace E U σ _).mpr
  intro a
  rw [← EmbeddingHodgeType.CM.projection_commutes_of_preserves H.complementary
    ((WeightOne.CM.scalarEndomorphism E a).baseChange ℂ)
    (h.hodge_action a) (fun y hy => (h.hodge_action a).map_antiholomorphic hy),
    (EmbeddingDecomposition.CM.mem_embeddingSpace E U σ x).mp hx a, map_smul]

include h in
/-- Each actual embedding line has one pure Hodge type. -/
theorem WeightOne.CM.RankOneCMAction.embeddingSpace_hodge_dichotomy (σ : E →ₐ[ℚ] ℂ) :
    EmbeddingDecomposition.CM.embeddingSpace E U σ ≤ H.holomorphic ∨ EmbeddingDecomposition.CM.embeddingSpace E U σ ≤ H.antiholomorphic := by
  let v := h.embeddingBasis σ
  have hv : v ∈ EmbeddingDecomposition.CM.embeddingSpace E U σ :=
    (EmbeddingDecomposition.CM.mem_embeddingSpace E U σ v).mpr (fun a => h.embeddingBasis_eigen a σ)
  let p := H.holomorphic.projection H.antiholomorphic H.complementary v
  by_cases hp : p = 0
  · right
    rw [h.embeddingSpace_eq_span]
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    exact (Submodule.projection_apply_eq_zero_iff H.complementary).mp hp
  · left
    have hspan := eq_span_singleton_of_mem_of_finrank_eq_one
      (h.embeddingSpace_finrank σ) (h.holomorphicProjection_mem_embeddingSpace σ hv) hp
    rw [hspan]
    apply (Submodule.span_singleton_le_iff_mem _ _).mpr
    exact Submodule.projection_apply_mem H.complementary v

include h in
/-- A nonzero embedding line cannot have both weight-one Hodge types. -/
theorem WeightOne.CM.RankOneCMAction.embeddingSpace_not_both_types (σ : E →ₐ[ℚ] ℂ) :
    ¬ (EmbeddingDecomposition.CM.embeddingSpace E U σ ≤ H.holomorphic ∧
      EmbeddingDecomposition.CM.embeddingSpace E U σ ≤ H.antiholomorphic) := by
  rintro ⟨hh, ha⟩
  have hv : h.embeddingBasis σ ∈ EmbeddingDecomposition.CM.embeddingSpace E U σ :=
    (EmbeddingDecomposition.CM.mem_embeddingSpace E U σ _).mpr (fun a => h.embeddingBasis_eigen a σ)
  have hboth : h.embeddingBasis σ ∈ H.holomorphic ⊓ H.antiholomorphic := ⟨hh hv, ha hv⟩
  rw [H.complementary.inf_eq_bot] at hboth
  exact h.embeddingBasis.ne_zero σ hboth

include h in
/-- The two possible types are exhaustive and mutually exclusive. -/
theorem WeightOne.CM.RankOneCMAction.embeddingSpace_antiholomorphic_iff_not_holomorphic (σ : E →ₐ[ℚ] ℂ) :
    EmbeddingDecomposition.CM.embeddingSpace E U σ ≤ H.antiholomorphic ↔ ¬ EmbeddingDecomposition.CM.embeddingSpace E U σ ≤ H.holomorphic := by
  constructor
  · intro ha hh
    exact h.embeddingSpace_not_both_types σ ⟨hh, ha⟩
  · intro hh
    exact (h.embeddingSpace_hodge_dichotomy σ).resolve_left hh

/-- The sign attached to the actual embedding line is positive precisely
when that line is holomorphic. -/
def WeightOne.CM.RankOneCMAction.embeddingSign (_h : WeightOne.CM.RankOneCMAction E H) (σ : E →ₐ[ℚ] ℂ) : Bool :=
  decide (EmbeddingDecomposition.CM.embeddingSpace E U σ ≤ H.holomorphic)

omit [NumberField E] [IsScalarTower ℚ E U] in
/-- Conjugation interchanges the actual embedding types. -/
theorem WeightOne.CM.RankOneCMAction.conjugate_embeddingSpace_holomorphic_iff (σ : E →ₐ[ℚ] ℂ) :
    EmbeddingDecomposition.CM.embeddingSpace E U (EmbeddingHodgeType.CM.conjugateEmbedding σ) ≤ H.holomorphic ↔
      EmbeddingDecomposition.CM.embeddingSpace E U σ ≤ H.antiholomorphic := by
  constructor
  · intro hc x hx
    have hx' := hc (EmbeddingHodgeType.CM.coefficientConjugation_mem_embeddingSpace E U σ hx)
    have hx'' := (H.conjugate_mem (WeightOne.CM.coefficientConjugation U x)).mpr hx'
    simpa using hx''
  · intro ha x hx
    have hx' := EmbeddingHodgeType.CM.coefficientConjugation_mem_embeddingSpace E U (EmbeddingHodgeType.CM.conjugateEmbedding σ) hx
    rw [EmbeddingHodgeType.CM.conjugateEmbedding_involutive] at hx'
    exact (H.conjugate_mem x).mp (ha hx')

include h in
/-- The signs of conjugate embedding lines are opposite. -/
theorem WeightOne.CM.RankOneCMAction.embeddingSign_conjugate (σ : E →ₐ[ℚ] ℂ) :
    h.embeddingSign (EmbeddingHodgeType.CM.conjugateEmbedding σ) = !h.embeddingSign σ := by
  simp only [WeightOne.CM.RankOneCMAction.embeddingSign, WeightOne.CM.RankOneCMAction.conjugate_embeddingSpace_holomorphic_iff,
    h.embeddingSpace_antiholomorphic_iff_not_holomorphic, decide_not]

include h in
/-- The integer signs used in the switch argument are odd under actual
embedding conjugation. -/
theorem WeightOne.CM.RankOneCMAction.embeddingSign_odd (σ : E →ₐ[ℚ] ℂ) :
    SignSwitch.CM.signValue (h.embeddingSign (EmbeddingHodgeType.CM.conjugateEmbedding σ)) = -SignSwitch.CM.signValue (h.embeddingSign σ) := by
  rw [h.embeddingSign_conjugate, SignSwitch.CM.signValue_not]

/-- The actual basis vector has holomorphic type exactly when its sign is positive. -/
theorem WeightOne.CM.RankOneCMAction.embeddingBasis_mem_holomorphic_iff (σ : E →ₐ[ℚ] ℂ) :
    h.embeddingBasis σ ∈ H.holomorphic ↔ h.embeddingSign σ = true := by
  rw [← Submodule.span_singleton_le_iff_mem, ← h.embeddingSpace_eq_span]
  simp [WeightOne.CM.RankOneCMAction.embeddingSign]

/-- The actual basis vector has antiholomorphic type exactly when its sign is negative. -/
theorem WeightOne.CM.RankOneCMAction.embeddingBasis_mem_antiholomorphic_iff (σ : E →ₐ[ℚ] ℂ) :
    h.embeddingBasis σ ∈ H.antiholomorphic ↔ h.embeddingSign σ = false := by
  rw [← Submodule.span_singleton_le_iff_mem, ← h.embeddingSpace_eq_span,
    h.embeddingSpace_antiholomorphic_iff_not_holomorphic]
  simp [WeightOne.CM.RankOneCMAction.embeddingSign]

/-- The holomorphic projection keeps exactly the positively signed basis vectors. -/
theorem WeightOne.CM.RankOneCMAction.holomorphicProjection_embeddingBasis (σ : E →ₐ[ℚ] ℂ) :
    H.holomorphic.projection H.antiholomorphic H.complementary (h.embeddingBasis σ) =
      if h.embeddingSign σ then h.embeddingBasis σ else 0 := by
  by_cases hs : h.embeddingSign σ = true
  · simpa [hs] using Submodule.projection_apply_of_mem_left H.complementary
      ((h.embeddingBasis_mem_holomorphic_iff σ).mpr hs)
  · have hs' : h.embeddingSign σ = false := Bool.eq_false_iff.mpr hs
    simpa [hs'] using Submodule.projection_apply_of_mem_right H.complementary
      ((h.embeddingBasis_mem_antiholomorphic_iff σ).mpr hs')

/-- The Hodge subspace is the span of precisely the positively signed
embedding lines. Thus the signs describe the full Hodge decomposition. -/
theorem WeightOne.CM.RankOneCMAction.holomorphic_eq_span_embeddingBasis :
    H.holomorphic = Submodule.span ℂ
      {v | ∃ σ : E →ₐ[ℚ] ℂ, h.embeddingSign σ = true ∧ h.embeddingBasis σ = v} := by
  apply le_antisymm
  · intro x hx
    let P := H.holomorphic.projection H.antiholomorphic H.complementary
    have hp : P x = x := Submodule.projection_apply_of_mem_left H.complementary hx
    have he := congrArg P (h.embeddingBasis.sum_repr x)
    rw [hp] at he
    rw [← he]
    simp only [map_sum, map_smul]
    apply Submodule.sum_mem
    intro σ _
    change h.embeddingBasis.repr x σ •
      (H.holomorphic.projection H.antiholomorphic H.complementary (h.embeddingBasis σ)) ∈ _
    rw [h.holomorphicProjection_embeddingBasis]
    by_cases hs : h.embeddingSign σ = true
    · simp only [hs, ite_true]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, hs, rfl⟩)
    · simp [Bool.eq_false_iff.mpr hs]
  · apply Submodule.span_le.mpr
    rintro v ⟨σ, hs, rfl⟩
    exact (h.embeddingBasis_mem_holomorphic_iff σ).mpr hs

/-- The antiholomorphic subspace is the span of the negatively signed lines. -/
theorem WeightOne.CM.RankOneCMAction.antiholomorphic_eq_span_embeddingBasis :
    H.antiholomorphic = Submodule.span ℂ
      {v | ∃ σ : E →ₐ[ℚ] ℂ, h.embeddingSign σ = false ∧ h.embeddingBasis σ = v} := by
  apply le_antisymm
  · intro x hx
    let Q := H.antiholomorphic.projection H.holomorphic H.complementary.symm
    have hq : Q x = x := Submodule.projection_apply_of_mem_left H.complementary.symm hx
    have he := congrArg Q (h.embeddingBasis.sum_repr x)
    rw [hq] at he
    rw [← he]
    simp only [map_sum, map_smul]
    apply Submodule.sum_mem
    intro σ _
    by_cases hs : h.embeddingSign σ = false
    · have hm := (h.embeddingBasis_mem_antiholomorphic_iff σ).mpr hs
      have hb : Q (h.embeddingBasis σ) = h.embeddingBasis σ :=
        Submodule.projection_apply_of_mem_left H.complementary.symm hm
      rw [hb]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, hs, rfl⟩)
    · have hs' : h.embeddingSign σ = true := by
        cases heq : h.embeddingSign σ <;> simp_all
      have hm := (h.embeddingBasis_mem_holomorphic_iff σ).mpr hs'
      have hb : Q (h.embeddingBasis σ) = 0 :=
        Submodule.projection_apply_of_mem_right H.complementary.symm hm
      rw [hb, smul_zero]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro v ⟨σ, hs, rfl⟩
    exact (h.embeddingBasis_mem_antiholomorphic_iff σ).mpr hs

end

end OAI.AlgebraicGeometry.ComplexMultiplication
