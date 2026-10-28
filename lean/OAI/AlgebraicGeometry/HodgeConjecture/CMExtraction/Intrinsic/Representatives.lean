import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Period
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum

/-! # Representatives -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity

noncomputable section

/-! The actual PEL embedding list supplies a complete set of Galois
representatives, with its distinguished embedding equal to identity. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open scoped Classical

attribute [local instance] Multiplicity.nativePlaceDecidableEq Multiplicity.nativeTripleDecidableEq

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)

def nativePlaces (hP : P.IsAdmissible) (hμ : P.μ = E.val.toRingHom) : HeckeCycles.GeometricSource.CM.Places E where
  count := s
  representative := Multiplicity.Period.nativeArchLabel E P
  distinguished := P.distinguished
  identity := Multiplicity.Period.nativeArchLabel_active E P hμ
  complete := by
    have he : (fun i : Fin s × Bool => ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
        (if i.2 then ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * Multiplicity.Period.nativeArchLabel E P i.1 else Multiplicity.Period.nativeArchLabel E P i.1)) =
        (fun i : Fin s × Bool => if i.2 then ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i.1)
          else P.embeddings i.1) := by
      funext ⟨i, side⟩
      cases side with
      | false => exact (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).apply_symm_apply (P.embeddings i)
      | true =>
        change ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * Multiplicity.Period.nativeArchLabel E P i) = _
        rw [ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_conjugation]
        exact congrArg ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding ((ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).apply_symm_apply (P.embeddings i))
    have hb : Function.Bijective ((ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E) ∘
        (fun i : Fin s × Bool => if i.2 then ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * Multiplicity.Period.nativeArchLabel E P i.1
          else Multiplicity.Period.nativeArchLabel E P i.1)) :=
      (congrArg (fun f : (Fin s × Bool) → (E →ₐ[ℚ] ℂ) => Function.Bijective f) he).mpr hP.1
    exact ⟨fun i j hij => hb.1 (congrArg (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E) hij), fun τ => by
      obtain ⟨i, hi⟩ := hb.2 (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)
      exact ⟨i, (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).injective hi⟩⟩

def nativeRepresentatives : Finset Gal(E/ℚ) := Finset.univ.image (Multiplicity.Period.nativeArchLabel E P)

theorem nativeArchLabel_injective (hP : P.IsAdmissible) (hμ : P.μ = E.val.toRingHom) :
    Function.Injective (Multiplicity.Period.nativeArchLabel E P) := by
  intro i j hij
  exact congrArg Prod.fst ((nativePlaces E P hP hμ).complete.1
    (a₁ := (i, false)) (a₂ := (j, false)) hij)

theorem nativeRepresentatives_prod {M : Type*} [CommMonoid M]
    (hP : P.IsAdmissible) (hμ : P.μ = E.val.toRingHom) (f : Gal(E/ℚ) → M) :
    (∏ τ ∈ nativeRepresentatives E P, f τ) = ∏ i : Fin s, f (Multiplicity.Period.nativeArchLabel E P i) := by
  exact Finset.prod_image (nativeArchLabel_injective E P hP hμ).injOn

theorem nativeRepresentatives_erase_prod {M : Type*} [CommMonoid M]
    (hP : P.IsAdmissible) (hμ : P.μ = E.val.toRingHom) (f : Gal(E/ℚ) → M) :
    (∏ τ ∈ (nativeRepresentatives E P).erase 1, f τ) =
      ∏ i ∈ (Finset.univ : Finset (Fin s)).erase P.distinguished, f (Multiplicity.Period.nativeArchLabel E P i) := by
  have he := Finset.image_erase (nativeArchLabel_injective E P hP hμ) Finset.univ P.distinguished
  rw [Multiplicity.Period.nativeArchLabel_active E P hμ] at he
  change (∏ τ ∈ (Finset.univ.image (Multiplicity.Period.nativeArchLabel E P)).erase 1, f τ) = _
  rw [← he]
  exact Finset.prod_image (nativeArchLabel_injective E P hP hμ).injOn

omit [NumberField E] [NumberField.IsCMField E] in
theorem nativeRepresentatives_active (hμ : P.μ = E.val.toRingHom) :
    (1 : Gal(E/ℚ)) ∈ nativeRepresentatives E P :=
  Finset.mem_image.mpr ⟨P.distinguished, Finset.mem_univ _, Multiplicity.Period.nativeArchLabel_active E P hμ⟩

theorem nativeRepresentatives_paired (hP : P.IsAdmissible) (hμ : P.μ = E.val.toRingHom)
    (τ : Gal(E/ℚ)) :
    τ ∈ nativeRepresentatives E P ↔ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ nativeRepresentatives E P := by
  let places := nativePlaces E P hP hμ
  have hi := places.complete.1
  constructor
  · intro hτ hct
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hτ
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hct
    have hp : (i, true) = (j, false) := hi hj.symm
    exact Bool.false_ne_true (congrArg Prod.snd hp).symm
  · intro hn
    obtain ⟨⟨i, side⟩, he⟩ := places.complete.2 τ
    cases side with
    | false => exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, he⟩
    | true =>
      apply False.elim
      apply hn
      refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, ?_⟩
      change ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * Multiplicity.Period.nativeArchLabel E P i = τ at he
      rw [← he, ← mul_assoc]
      have hc : ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E = 1 := by
        apply AlgEquiv.ext
        exact ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_apply_apply E
      rw [hc, one_mul]

theorem native_halfDet_identity (hP : P.IsAdmissible) (hμ : P.μ = E.val.toRingHom)
    (v : Multiplicity.Odd.Sign E) (r : Eˣ) (h : ℂ)
    (hh : h ^ 2 = (P.embeddings P.distinguished (r : E))⁻¹ *
      ∏ i ∈ (Finset.univ : Finset (Fin s)).erase P.distinguished,
        (P.embeddings i (r : E)) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (Multiplicity.Period.nativeCompactSigns E P v i))) :
    h ^ 2 = (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (r : E)) ^ (1 - 2 : ℤ) *
      ∏ τ ∈ (nativeRepresentatives E P).erase 1,
        (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E)) ^ (-3 * ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹)) := by
  rw [show (1 - 2 : ℤ) = -1 from rfl, zpow_neg_one,
    nativeRepresentatives_erase_prod E P hP hμ]
  simp only [ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_apply, Multiplicity.Period.nativeArchLabel_spec]
  have hact : P.embeddings P.distinguished (r : E) = ((r : E) : ℂ) := RingHom.congr_fun hμ (r : E)
  change h ^ 2 = ((r : E) : ℂ)⁻¹ * _
  rw [← hact]
  exact hh

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity
