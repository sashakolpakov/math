import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource

/-! # Representatives -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Representatives.CM

noncomputable section

/-! The source's ordered places give the actual Galois representative
set and its erased-product formula for RadialDilation. -/

open scoped Classical BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  (places : GeometricSource.CM.Places E)

theorem injective : Function.Injective places.representative := by
  intro i j h
  exact congrArg Prod.fst (places.complete.1 (a₁ := (i, false)) (a₂ := (j, false)) h)

theorem opposite_ne (i j : Fin places.count) :
    ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative i ≠ places.representative j := by
  intro h
  have h := congrArg Prod.snd (places.complete.1 (a₁ := (i, true)) (a₂ := (j, false)) h)
  exact Bool.noConfusion h

def representatives : Finset (Gal(E/ℚ)) := Finset.univ.image places.representative

theorem mem_iff (τ : Gal(E/ℚ)) : τ ∈ representatives E places ↔ ∃ i, places.representative i = τ := by
  simp only [representatives, Finset.mem_image, Finset.mem_univ, true_and]

theorem active : (1 : Gal(E/ℚ)) ∈ representatives E places :=
  (mem_iff E places 1).mpr ⟨places.distinguished, places.identity⟩

theorem paired (τ : Gal(E/ℚ)) :
    τ ∈ representatives E places ↔ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ representatives E places := by
  constructor
  · intro ht hc
    obtain ⟨i, rfl⟩ := (mem_iff E places τ).mp ht
    obtain ⟨j, hj⟩ := (mem_iff E places _).mp hc
    exact opposite_ne E places i j hj.symm
  · intro hc
    obtain ⟨⟨i, b⟩, hi⟩ := places.complete.2 τ
    cases b
    · exact (mem_iff E places τ).mpr ⟨i, hi⟩
    · exfalso
      apply hc
      apply (mem_iff E places _).mpr
      refine ⟨i, ?_⟩
      change ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * places.representative i = τ at hi
      rw [← hi]
      apply AlgEquiv.ext
      intro x
      exact (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation_apply_apply E (places.representative i x)).symm

theorem erase_image : (Finset.univ.erase places.distinguished).image places.representative =
    (representatives E places).erase 1 := by
  rw [Finset.image_erase (injective E places), places.identity]
  rfl

theorem product_erase {A : Type*} [CommMonoid A] (f : Gal(E/ℚ) → A) :
    (∏ i ∈ Finset.univ.erase places.distinguished, f (places.representative i)) =
      ∏ τ ∈ (representatives E places).erase 1, f τ := by
  rw [← erase_image]
  exact (Finset.prod_image (fun _ _ _ _ h => injective E places h)).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.Representatives.CM
