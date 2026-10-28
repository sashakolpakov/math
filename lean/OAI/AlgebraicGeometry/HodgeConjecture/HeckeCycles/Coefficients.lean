import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Definitions
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.AlgebraicClosure

/-! # Coefficients -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM

noncomputable section

/-!
# Finite coefficient fields for HeckeCycles

A finite collection of tensors with algebraic coefficients is defined over
one finite Galois field containing E. The field is constructed by adjoining
the finitely many coefficients and taking the normal closure. For a projector
defined over that field, the complex range is the scalar span of the actual
coefficient-field range. Neither assertion assumes CM extraction.
-/

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Definitions.CM

/-- The actual subfield of complex numbers algebraic over ℚ. -/
abbrev algebraicField : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

instance algebraicField_isAlgClosed : IsAlgClosed algebraicField :=
  (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed

instance algebraicField_isAlgebraic : Algebra.IsAlgebraic ℚ algebraicField :=
  algebraicClosure.isAlgebraic ℚ ℂ

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E]

/-- One finite Galois coefficient field, built from a finite algebraic set. -/
def fieldFor (E : IntermediateField ℚ ℂ) [NumberField E]
    (s : Finset ℂ) (hs : ∀ z ∈ s, IsAlgebraic ℚ z) :
    FiniteGaloisIntermediateField ℚ ℂ := by
  let L := IntermediateField.adjoin ℚ (s : Set ℂ)
  letI : FiniteDimensional ℚ L :=
    IntermediateField.finiteDimensional_adjoin (fun z hz => (hs z hz).isIntegral)
  let B := E ⊔ L
  letI : FiniteDimensional ℚ B := inferInstance
  let J := IntermediateField.normalClosure ℚ B ℂ
  let hJ : Normal ℚ J :=
    (Algebra.IsAlgebraic.isNormalClosure_normalClosure
      (F := ℚ) (K := B) (L := ℂ) (fun _ => IsAlgClosed.splits _)).normal
  exact {
    toIntermediateField := J
    finiteDimensional := inferInstance
    isGalois := {
      to_isSeparable := inferInstance
      to_normal := hJ } }

omit [IsGalois ℚ E] in
theorem fieldFor_contains (s : Finset ℂ) (hs : ∀ z ∈ s, IsAlgebraic ℚ z) :
    E ≤ (fieldFor E s hs).toIntermediateField ∧
      ∀ z ∈ s, z ∈ (fieldFor E s hs).toIntermediateField := by
  refine ⟨le_sup_left.trans (IntermediateField.le_normalClosure
    (E ⊔ IntermediateField.adjoin ℚ (s : Set ℂ))), ?_⟩
  intro z hz
  apply IntermediateField.le_normalClosure (E ⊔ IntermediateField.adjoin ℚ (s : Set ℂ))
  exact (show IntermediateField.adjoin ℚ (s : Set ℂ) ≤
    E ⊔ IntermediateField.adjoin ℚ (s : Set ℂ) from le_sup_right)
      (IntermediateField.subset_adjoin ℚ _ hz)

variable {M : Type*} [AddCommGroup M] [Module ℚ M]

omit [NumberField E] [IsGalois ℚ E] in
/-- Tensor induction records the actual finite coefficients needed by a vector. -/
theorem finite_tensor_coefficients
    (A : IntermediateField ℚ ℂ) [hA : Algebra.IsAlgebraic ℚ A]
    (x : A ⊗[ℚ] M) :
    ∃ s : Finset ℂ, (∀ z ∈ s, IsAlgebraic ℚ z) ∧
      ∀ K : IntermediateField ℚ ℂ, (∀ z ∈ s, z ∈ K) →
        ∃ y : K ⊗[ℚ] M, ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K M y = ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion A M x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m =>
      refine ⟨{(a : ℂ)}, ?_, ?_⟩
      · intro z hz
        have hz' : z = (a : ℂ) := Finset.mem_singleton.mp hz
        rw [hz']
        exact IsAlgebraic.algHom A.val (hA.isAlgebraic a)
      · intro K hK
        exact ⟨(⟨(a : ℂ), hK _ (Finset.mem_singleton_self _)⟩ : K) ⊗ₜ[ℚ] m, rfl⟩
  | add x y hx hy =>
      obtain ⟨sx, hsx, hxlift⟩ := hx
      obtain ⟨sy, hsy, hylift⟩ := hy
      refine ⟨sx ∪ sy, ?_, ?_⟩
      · intro z hz
        exact (Finset.mem_union.mp hz).elim (hsx z) (hsy z)
      · intro K hK
        obtain ⟨xK, hxK⟩ := hxlift K (fun z hz => hK z (Finset.mem_union_left _ hz))
        obtain ⟨yK, hyK⟩ := hylift K (fun z hz => hK z (Finset.mem_union_right _ hz))
        exact ⟨xK + yK, by rw [map_add, map_add, hxK, hyK]⟩

omit [IsGalois ℚ E] in
/-- All algebraic projector tensors can be placed over the same finite field. -/
theorem finite_galois_field_for_tensors
    (A : IntermediateField ℚ ℂ) [Algebra.IsAlgebraic ℚ A]
    {I : Type*} [Fintype I] (x : I → A ⊗[ℚ] M) :
    ∃ K : IntermediateField ℚ ℂ,
      NumberField K ∧ IsGalois ℚ K ∧ E ≤ K ∧
      ∀ i, ∃ y : K ⊗[ℚ] M, ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K M y = ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion A M (x i) := by
  choose s hs hlift using fun i => finite_tensor_coefficients A (x i)
  let total := Finset.univ.biUnion s
  have htotal : ∀ z ∈ total, IsAlgebraic ℚ z := by
    intro z hz
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hz
    exact hs i z hi
  let K := fieldFor E total htotal
  have hcontains := fieldFor_contains E total htotal
  refine ⟨K.toIntermediateField, NumberField.of_module_finite ℚ _, K.isGalois,
    hcontains.1, ?_⟩
  intro i
  apply hlift i K.toIntermediateField
  intro z hz
  exact hcontains.2 z (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hz⟩)

omit [NumberField E] in
theorem all_embeddings_in_field [NumberField.IsCMField E]
    (K : IntermediateField ℚ ℂ) (hEK : E ≤ K) :
    ∀ τ : E →ₐ[ℚ] ℂ, τ.fieldRange ≤ K := by
  intro τ
  obtain ⟨g, rfl⟩ := (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).surjective τ
  rintro z ⟨a, rfl⟩
  exact hEK (g a).property

/-- Restriction of scalar conjugation to E, expressed through actual embeddings. -/
def coefficientRestriction [NumberField.IsCMField E]
    (K : IntermediateField ℚ ℂ)
    (hK : ∀ τ : E →ₐ[ℚ] ℂ, τ.fieldRange ≤ K) (σ : Gal(K/ℚ)) : Gal(E/ℚ) :=
  (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).symm
    (ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK σ (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1))

omit [NumberField E] in
theorem coefficientRestriction_spec [NumberField.IsCMField E]
    (K : IntermediateField ℚ ℂ)
    (hK : ∀ τ : E →ₐ[ℚ] ℂ, τ.fieldRange ≤ K) (σ : Gal(K/ℚ)) :
    ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK σ (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1) =
      ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (coefficientRestriction E K hK σ) :=
  ((ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).apply_symm_apply _).symm

omit [NumberField E] in
theorem coefficientRestriction_one [NumberField.IsCMField E]
    (K : IntermediateField ℚ ℂ)
    (hK : ∀ τ : E →ₐ[ℚ] ℂ, τ.fieldRange ≤ K) :
    coefficientRestriction E K hK 1 = 1 := by
  apply (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).injective
  rw [← coefficientRestriction_spec, ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding_one]

omit [NumberField E] [IsGalois ℚ E] in
theorem scalarConjugate_identity (K : IntermediateField ℚ ℂ)
    (x : K ⊗[ℚ] M) : ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K M 1 x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a m => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

omit [NumberField E] [IsGalois ℚ E] in
/-- The range of the extended operator is the span of its coefficient-field range.
This gives CMExtraction's coefficient-space identification by construction. -/
theorem extended_range_eq_conjugateSpace
    (K : IntermediateField ℚ ℂ)
    (x : K ⊗[ℚ] (M →ₗ[ℚ] M)) :
    LinearMap.range (ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K M M x) =
      CMExtraction.Definitions.CM.conjugateSpace K (LinearMap.range (ComplexMultiplication.HomBaseChange.CM.homBaseChange K M M x)) 1 := by
  let Q := ComplexMultiplication.HomBaseChange.CM.homBaseChange K M M x
  let P := ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients K M M x
  let S := CMExtraction.Definitions.CM.conjugateSpace K (LinearMap.range Q) 1
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    change P w ∈ S
    induction w using TensorProduct.inductionOn with
    | add y z hy hz => simpa only [map_add] using S.add_mem hy hz
    | tmul a m =>
        have hmem : ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K M (Q ((1 : K) ⊗ₜ[ℚ] m)) ∈ S := by
          apply Submodule.subset_span
          exact ⟨Q ((1 : K) ⊗ₜ[ℚ] m), ⟨(1 : K) ⊗ₜ[ℚ] m, rfl⟩,
            by rw [scalarConjugate_identity]⟩
        have heq := ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients_apply_inclusion K M M x ((1 : K) ⊗ₜ[ℚ] m)
        simp only [ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion_tmul, IntermediateField.coe_one] at heq
        have hm : P ((1 : ℂ) ⊗ₜ[ℚ] m) ∈ S := heq.symm ▸ hmem
        have ha := S.smul_mem a hm
        simpa only [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one] using ha
  · apply Submodule.span_le.mpr
    rintro z ⟨y, ⟨w, rfl⟩, rfl⟩
    rw [scalarConjugate_identity]
    exact ⟨ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K M w, ComplexMultiplication.Hodge.MapDescent.CM.complexHomOfCoefficients_apply_inclusion K M M x w⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM
