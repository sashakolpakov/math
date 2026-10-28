import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal

/-! # Localization Numerator -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.LocalizationNumerator

noncomputable section

/-! A polynomial in an extended ideal has a numerator in the original
ideal and a denominator in the coefficient ring. -/

open _root_.MvPolynomial

universe u v w
variable {R : Type u} [CommRing R] {σ : Type v}

theorem polynomial_ideal_localization_numerator (U : Submonoid R)
    (S : Type w) [CommRing S] [Algebra R S] [IsLocalization U S]
    (I : Ideal (MvPolynomial σ R)) (g : MvPolynomial σ S)
    (hg : g ∈ I.map (MvPolynomial.map (algebraMap R S))) :
    ∃ (f : MvPolynomial σ R), f ∈ I ∧ ∃ s : U,
      MvPolynomial.map (algebraMap R S) f = g * C (algebraMap R S s.val) := by
  let : Algebra (MvPolynomial σ R) (MvPolynomial σ S) := MvPolynomial.algebraMvPolynomial
  change g ∈ I.map (algebraMap (MvPolynomial σ R) (MvPolynomial σ S)) at hg
  obtain ⟨⟨f, d⟩, hd⟩ := (IsLocalization.mem_map_algebraMap_iff
    (U.map (C (σ := σ))) (MvPolynomial σ S)).mp hg
  obtain ⟨s, hs, hsd⟩ := d.property
  refine ⟨f.val, f.property, ⟨s, hs⟩, ?_⟩
  change g * MvPolynomial.map (algebraMap R S) d.val =
    MvPolynomial.map (algebraMap R S) f.val at hd
  rw [← hsd, MvPolynomial.map_C] at hd
  exact hd.symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.LocalizationNumerator
