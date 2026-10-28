import OAI.AlgebraicGeometry.ComplexMultiplication.CommonCMField
import OAI.AlgebraicGeometry.ComplexMultiplication.DecompositionEmbeddingBasis

/-! # Galois Signs -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication

noncomputable section

/-!
# Odd Hodge sign functions on a common finite Galois group

The actual CM summands can have different fields. Their embedding indices
nevertheless carry an action of one common finite Galois group. Complex
conjugation is central in that group and reverses the Hodge sign of every
index. This supplies the sign functions used in the tensor reduction.
-/

namespace GaloisSigns.CM.CMCoefficientField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]

/-- Intrinsic CM conjugation, regarded as a rational automorphism. -/
def conjugation : Gal(K/ℚ) :=
  (NumberField.IsCMField.complexConj K).restrictScalars ℚ

@[simp]
theorem conjugation_coe (x : K) : (conjugation K x : ℂ) = star (x : ℂ) :=
  NumberField.IsCMField.complexEmbedding_complexConj K K.val.toRingHom x

/-- The same automorphism induces complex conjugation at every embedding. -/
theorem embedding_conjugation (φ : K →+* ℂ) (x : K) :
    φ (conjugation K x) = star (φ x) :=
  NumberField.IsCMField.complexEmbedding_complexConj K φ x

@[simp]
theorem conjugation_apply_apply (x : K) : conjugation K (conjugation K x) = x :=
  NumberField.IsCMField.complexConj_apply_apply K x

/-- Complex conjugation is central among rational automorphisms of a CM field. -/
theorem conjugation_commute (g : Gal(K/ℚ)) : Commute (conjugation K) g := by
  apply AlgEquiv.ext
  intro x
  apply K.val.injective
  change (conjugation K (g x) : ℂ) = (g (conjugation K x) : ℂ)
  rw [conjugation_coe]
  exact (embedding_conjugation K (K.val.toRingHom.comp g.toRingHom) x).symm

theorem conjugation_ne_one : conjugation K ≠ 1 := by
  intro h
  apply NumberField.IsCMField.complexConj_ne_one K
  apply AlgEquiv.ext
  intro x
  exact congrArg (fun g : Gal(K/ℚ) => g x) h

end GaloisSigns.CM.CMCoefficientField

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
variable {H : WeightOne.CM.WeightOneHodgeStructure U} (D : Decomposition.CM.CMDecomposition H)

/-- A common field containing all embeddings of every actual CM component. -/
def Decomposition.CM.CMDecomposition.commonCoefficientField : IntermediateField ℚ ℂ :=
  D.exists_common_galois_cm_field.choose

instance Decomposition.CM.CMDecomposition.commonCoefficientField_numberField : NumberField D.commonCoefficientField :=
  D.exists_common_galois_cm_field.choose_spec.1

instance Decomposition.CM.CMDecomposition.commonCoefficientField_isGalois : IsGalois ℚ D.commonCoefficientField :=
  D.exists_common_galois_cm_field.choose_spec.2.1

instance Decomposition.CM.CMDecomposition.commonCoefficientField_isCMField : NumberField.IsCMField D.commonCoefficientField :=
  D.exists_common_galois_cm_field.choose_spec.2.2.1

theorem Decomposition.CM.CMDecomposition.fieldRange_le_commonCoefficientField (i : Fin D.numberOfComponents)
    (σ : (D.component i).field →ₐ[ℚ] ℂ) : σ.fieldRange ≤ D.commonCoefficientField :=
  D.exists_common_galois_cm_field.choose_spec.2.2.2 i σ

/-- Lift an embedding of a component to the common field without changing its values. -/
def Decomposition.CM.CMDecomposition.embeddingToCommonField (i : Fin D.numberOfComponents)
    (σ : (D.component i).field →ₐ[ℚ] ℂ) :
    (D.component i).field →ₐ[ℚ] D.commonCoefficientField :=
  σ.codRestrict _ (fun x => D.fieldRange_le_commonCoefficientField i σ ⟨x, rfl⟩)

@[simp]
theorem Decomposition.CM.CMDecomposition.embeddingToCommonField_coe (i : Fin D.numberOfComponents)
    (σ : (D.component i).field →ₐ[ℚ] ℂ) (x : (D.component i).field) :
    (D.embeddingToCommonField i σ x : ℂ) = σ x := rfl

/-- The common Galois group acts on each component's complex embeddings. -/
def Decomposition.CM.CMDecomposition.galoisEmbedding (g : Gal(D.commonCoefficientField/ℚ)) (i : Fin D.numberOfComponents)
    (σ : (D.component i).field →ₐ[ℚ] ℂ) : (D.component i).field →ₐ[ℚ] ℂ :=
  D.commonCoefficientField.val.comp (g.toAlgHom.comp (D.embeddingToCommonField i σ))

@[simp]
theorem Decomposition.CM.CMDecomposition.embeddingToCommonField_galoisEmbedding (g : Gal(D.commonCoefficientField/ℚ))
    (i : Fin D.numberOfComponents) (σ : (D.component i).field →ₐ[ℚ] ℂ)
    (x : (D.component i).field) :
    D.embeddingToCommonField i (D.galoisEmbedding g i σ) x =
      g (D.embeddingToCommonField i σ x) := by
  apply Subtype.ext
  rfl

@[simp]
theorem Decomposition.CM.CMDecomposition.galoisEmbedding_one (i : Fin D.numberOfComponents)
    (σ : (D.component i).field →ₐ[ℚ] ℂ) : D.galoisEmbedding 1 i σ = σ := by
  ext x
  rfl

theorem Decomposition.CM.CMDecomposition.galoisEmbedding_mul (g h : Gal(D.commonCoefficientField/ℚ))
    (i : Fin D.numberOfComponents) (σ : (D.component i).field →ₐ[ℚ] ℂ) :
    D.galoisEmbedding (g * h) i σ = D.galoisEmbedding g i (D.galoisEmbedding h i σ) := by
  ext x
  change (g (h (D.embeddingToCommonField i σ x)) : ℂ) =
    (g (D.embeddingToCommonField i (D.galoisEmbedding h i σ) x) : ℂ)
  rw [Decomposition.CM.CMDecomposition.embeddingToCommonField_galoisEmbedding]

/-- The Galois action retains the original direct-sum component. -/
def Decomposition.CM.CMDecomposition.galoisIndex (g : Gal(D.commonCoefficientField/ℚ)) (j : D.EmbeddingIndex) :
    D.EmbeddingIndex := ⟨j.1, D.galoisEmbedding g j.1 j.2⟩

@[simp]
theorem Decomposition.CM.CMDecomposition.galoisIndex_one (j : D.EmbeddingIndex) : D.galoisIndex 1 j = j := by
  rcases j with ⟨i, σ⟩
  exact congrArg (fun τ => (⟨i, τ⟩ : D.EmbeddingIndex)) (D.galoisEmbedding_one i σ)

theorem Decomposition.CM.CMDecomposition.galoisIndex_mul (g h : Gal(D.commonCoefficientField/ℚ)) (j : D.EmbeddingIndex) :
    D.galoisIndex (g * h) j = D.galoisIndex g (D.galoisIndex h j) := by
  rcases j with ⟨i, σ⟩
  exact congrArg (fun τ => (⟨i, τ⟩ : D.EmbeddingIndex)) (D.galoisEmbedding_mul g h i σ)

/-- Galois conjugation gives the same index involution as complex conjugation. -/
theorem Decomposition.CM.CMDecomposition.galoisIndex_conjugation (j : D.EmbeddingIndex) :
    D.galoisIndex (GaloisSigns.CM.CMCoefficientField.conjugation D.commonCoefficientField) j =
      D.conjugateIndex j := by
  rcases j with ⟨i, σ⟩
  apply congrArg (fun τ => (⟨i, τ⟩ : D.EmbeddingIndex))
  ext x
  change (GaloisSigns.CM.CMCoefficientField.conjugation D.commonCoefficientField
      (D.embeddingToCommonField i σ x) : ℂ) = star (σ x)
  rw [GaloisSigns.CM.CMCoefficientField.conjugation_coe, Decomposition.CM.CMDecomposition.embeddingToCommonField_coe]

/-- The actual Hodge sign of an embedding line along its scalar Galois orbit. -/
def Decomposition.CM.CMDecomposition.galoisSign (j : D.EmbeddingIndex) (g : Gal(D.commonCoefficientField/ℚ)) : Bool :=
  D.embeddingSign (D.galoisIndex g j)

@[simp]
theorem Decomposition.CM.CMDecomposition.galoisSign_one (j : D.EmbeddingIndex) : D.galoisSign j 1 = D.embeddingSign j := by
  simp [Decomposition.CM.CMDecomposition.galoisSign]

/-- Every embedding line defines an odd sign function on one finite Galois group. -/
theorem Decomposition.CM.CMDecomposition.galoisSign_conjugation_mul (j : D.EmbeddingIndex)
    (g : Gal(D.commonCoefficientField/ℚ)) :
    D.galoisSign j (GaloisSigns.CM.CMCoefficientField.conjugation D.commonCoefficientField * g) =
      !D.galoisSign j g := by
  rw [Decomposition.CM.CMDecomposition.galoisSign, Decomposition.CM.CMDecomposition.galoisIndex_mul, Decomposition.CM.CMDecomposition.galoisIndex_conjugation, Decomposition.CM.CMDecomposition.embeddingSign_conjugate]
  rfl

theorem Decomposition.CM.CMDecomposition.galoisSign_odd (j : D.EmbeddingIndex) (g : Gal(D.commonCoefficientField/ℚ)) :
    SignSwitch.CM.signValue (D.galoisSign j (GaloisSigns.CM.CMCoefficientField.conjugation D.commonCoefficientField * g)) =
      -SignSwitch.CM.signValue (D.galoisSign j g) := by
  rw [Decomposition.CM.CMDecomposition.galoisSign_conjugation_mul]
  exact SignSwitch.CM.signValue_not _

end

end OAI.AlgebraicGeometry.ComplexMultiplication
