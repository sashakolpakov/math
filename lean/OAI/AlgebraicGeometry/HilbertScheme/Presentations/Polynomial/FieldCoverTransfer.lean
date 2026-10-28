import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.LeadingBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.MonicPolynomialQuotientFree

/-! # Field Cover Transfer -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.FieldCoverTransfer

noncomputable section

/-! A leading-term cover over an injective coefficient extension controls
the quotient over any intermediate ring where its leading coefficients
are units. -/

open _root_.MvPolynomial

universe u v w z t
variable {R : Type u} [CommRing R]
variable (A : Type v) [CommRing A] [Algebra R A]
variable (K : Type w) [CommRing K] [Algebra R K] [Algebra A K] [IsScalarTower R A K]
variable {σ : Type z}

theorem polynomial_ideal_map_tower (I : Ideal (MvPolynomial σ R)) :
    (I.map (MvPolynomial.map (algebraMap R A))).map (MvPolynomial.map (algebraMap A K)) =
      I.map (MvPolynomial.map (algebraMap R K)) := by
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro f
  simp only [RingHom.comp_apply, MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq R A K]

theorem polynomial_quotient_free_of_field_cover
    (hAK : Function.Injective (algebraMap A K)) (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ R)) {ι : Type t} (b : ι → MvPolynomial σ R)
    (hb : ∀ i, b i ∈ I)
    (hu : ∀ i, IsUnit (m.leadingCoeff (MvPolynomial.map (algebraMap R A) (b i))))
    (hc : ∀ g ∈ I.map (MvPolynomial.map (algebraMap R K)), g ≠ 0 →
      ∃ i, m.degree (MvPolynomial.map (algebraMap R K) (b i)) ≤ m.degree g) :
    Module.Free A (MvPolynomial σ A ⧸ I.map (MvPolynomial.map (algebraMap R A))) := by
  apply MonicPolynomialQuotientFree.monic_leading_cover_quotient_free m _
    (fun i => MvPolynomial.map (algebraMap R A) (b i))
    (fun i => Ideal.mem_map_of_mem _ (hb i)) hu
  intro f hf hf0
  have hmap : MvPolynomial.map (algebraMap A K) f ∈
      I.map (MvPolynomial.map (algebraMap R K)) := by
    rw [← polynomial_ideal_map_tower A K I]
    exact Ideal.mem_map_of_mem _ hf
  have hmap0 : MvPolynomial.map (algebraMap A K) f ≠ 0 := by
    intro hz
    exact hf0 (MvPolynomial.map_injective _ hAK (hz.trans (map_zero _).symm))
  obtain ⟨i, hi⟩ := hc _ hmap hmap0
  refine ⟨i, ?_⟩
  have he : MvPolynomial.map (algebraMap R K) (b i) =
      MvPolynomial.map (algebraMap A K) (MvPolynomial.map (algebraMap R A) (b i)) := by
    simp only [MvPolynomial.map_map, ← IsScalarTower.algebraMap_eq R A K]
  rw [he, LeadingBaseChange.polynomial_leading_degree_map m _ hAK, LeadingBaseChange.polynomial_leading_degree_map m _ hAK] at hi
  exact hi

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.FieldCoverTransfer
