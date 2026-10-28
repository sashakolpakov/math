import OAI.RepresentationTheory.Hecke.RadialDilation.SplitPairedTrace

/-! # Representative Embeddings -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.RepresentativeEmbeddings.Realization

noncomputable section

section

/-! The Galois representative set supplies both archimedean and split local embedding labels. -/

open scoped Classical

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]

def representativePair (reps : Finset Gal(E/ℚ)) : reps × Bool → Gal(E/ℚ) :=
  fun p => if p.2 then AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * p.1.val else p.1.val

omit [IsGalois ℚ E] in
theorem conjugation_mul_twice (τ : Gal(E/ℚ)) : AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) = τ := by
  apply AlgEquiv.ext
  intro x
  exact AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_apply_apply E (τ x)

omit [IsGalois ℚ E] in
theorem representativePair_bijective (reps : Finset Gal(E/ℚ))
    (hreps : ∀ τ, τ ∈ reps ↔ AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ reps) :
    Function.Bijective (representativePair E reps) := by
  constructor
  · rintro ⟨a, i⟩ ⟨b, j⟩ h
    cases i <;> cases j
    · have he : a.val = b.val := h
      exact Prod.ext (Subtype.ext he) rfl
    · have he : a.val = AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * b.val := h
      exact False.elim (((hreps b.val).mp b.property) (he ▸ a.property))
    · have he : AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * a.val = b.val := h
      exact False.elim (((hreps a.val).mp a.property) (he.symm ▸ b.property))
    · have he : AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * a.val = AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * b.val := h
      exact Prod.ext (Subtype.ext (mul_left_cancel he)) rfl
  · intro τ
    by_cases hτ : τ ∈ reps
    · exact ⟨(⟨τ, hτ⟩, false), rfl⟩
    · have hc : AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∈ reps := by
        apply (hreps _).mpr
        rw [conjugation_mul_twice]
        exact hτ
      exact ⟨(⟨AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ, hc⟩, true), conjugation_mul_twice E τ⟩

def complexRepresentativeEmbeddings (reps : Finset Gal(E/ℚ)) : reps → E →ₐ[ℚ] ℂ :=
  fun τ => AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ.val

theorem complexRepresentativeEmbeddings_paired (reps : Finset Gal(E/ℚ))
    (hreps : ∀ τ, τ ∈ reps ↔ AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ reps) :
    Function.Bijective (Complexification.Realization.pairingEmbeddings (complexRepresentativeEmbeddings E reps)) := by
  have he : Complexification.Realization.pairingEmbeddings (complexRepresentativeEmbeddings E reps) =
      (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E) ∘ representativePair E reps := by
    funext p
    rcases p with ⟨τ, b⟩
    cases b
    · rfl
    · exact (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_conjugation E τ.val).symm
  rw [he]
  exact (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).bijective.comp (representativePair_bijective E reps hreps)

variable (K : Type*) [Field K] [Algebra ℚ K] [Algebra E K] [IsScalarTower ℚ E K]

def splitGaloisEmbeddingEquiv : Gal(E/ℚ) ≃ (E →ₐ[ℚ] K) := (Normal.algHomEquivAut ℚ K E).symm

theorem splitGaloisEmbeddingEquiv_conjugation (τ : Gal(E/ℚ)) :
    splitGaloisEmbeddingEquiv E K (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) =
      SplitTrace.Realization.conjugateSplitEmbedding E K (splitGaloisEmbeddingEquiv E K τ) := by
  ext x
  change algebraMap E K ((AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ) x) = algebraMap E K ((τ * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) x)
  rw [(AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_commute E τ).eq]

def splitRepresentativeEmbeddings (reps : Finset Gal(E/ℚ)) : reps → E →ₐ[ℚ] K :=
  fun τ => splitGaloisEmbeddingEquiv E K τ.val

theorem splitRepresentativeEmbeddings_paired (reps : Finset Gal(E/ℚ))
    (hreps : ∀ τ, τ ∈ reps ↔ AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ reps) :
    Function.Bijective (SplitPairedTrace.Realization.splitPairingEmbeddings E K (splitRepresentativeEmbeddings E K reps)) := by
  have he : SplitPairedTrace.Realization.splitPairingEmbeddings E K (splitRepresentativeEmbeddings E K reps) =
      (splitGaloisEmbeddingEquiv E K) ∘ representativePair E reps := by
    funext p
    rcases p with ⟨τ, b⟩
    cases b
    · rfl
    · exact (splitGaloisEmbeddingEquiv_conjugation E K τ.val).symm
  rw [he]
  exact (splitGaloisEmbeddingEquiv E K).bijective.comp (representativePair_bijective E reps hreps)

end

/-! Convert the concrete representative-index determinant into RadialDilation's Galois-index product. -/

open scoped Classical

theorem representative_erase_product {I A : Type*} [DecidableEq I] [CommMonoid A]
    (s : Finset I) (i : s) (f : I → A) :
    ∏ j ∈ (Finset.univ : Finset s).erase i, f j.val = ∏ j ∈ s.erase i.val, f j := by
  rw [Finset.univ_eq_attach]
  exact Finset.prod_erase_attach f i

theorem representative_erase_product_with_decidable {I A : Type*} [DecidableEq I] [CommMonoid A]
    (s : Finset I) (ds : DecidableEq s) (i : s) (f : I → A) :
    ∏ j ∈ @Finset.erase s ds Finset.univ i, f j.val = ∏ j ∈ s.erase i.val, f j := by
  have hd : ds = (fun a b : s => a.instDecidableEq b) := Subsingleton.elim _ _
  subst ds
  rw [Finset.univ_eq_attach]
  exact Finset.prod_erase_attach f i

theorem representative_halfDet_identity
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    (reps : Finset Gal(E/ℚ)) (hactive : (1 : Gal(E/ℚ)) ∈ reps)
    (d : Gal(E/ℚ) → Bool) (r : Eˣ) (h : ℂ)
    (hh : h ^ 2 = (complexRepresentativeEmbeddings E reps ⟨1, hactive⟩ (r : E))⁻¹ *
      ∏ τ ∈ @Finset.erase reps (Classical.decEq reps) Finset.univ ⟨1, hactive⟩,
        complexRepresentativeEmbeddings E reps τ (r : E) ^ (-3 * AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (d τ.val))) :
    h ^ 2 = (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (r : E)) ^ (1 - 2 : ℤ) *
      ∏ τ ∈ reps.erase 1, AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E) ^ (-3 * AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (d τ)) := by
  rw [show (1 - 2 : ℤ) = -1 from rfl, zpow_neg_one]
  have hp := representative_erase_product_with_decidable reps (Classical.decEq reps) ⟨1, hactive⟩
    (fun τ => AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E) ^ (-3 * AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (d τ)))
  simp only [complexRepresentativeEmbeddings] at hh
  rw [hp] at hh
  exact hh

end

end OAI.RepresentationTheory.Hecke.RadialDilation.RepresentativeEmbeddings.Realization
