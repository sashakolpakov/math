import OAI.ArithmeticGeometry.Models.SpreadingOut.PolynomialCoordinates
import OAI.ArithmeticGeometry.Models.CoefficientSystem

/-! # Hypersurface Coefficients -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceCoefficients.Construction

noncomputable section

/-! A monic hypersurface equation and its chart denominator are defined over
one finite coefficient subalgebra. -/

universe u

open OAI.ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations

theorem monic_hypersurface_coefficients_descend
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (n : ℕ) (p : Polynomial (MvPolynomial (Fin n) K)) (hp : p.Monic)
    (d : MvPolynomial (Fin n) K) :
    ∃ (s : Finset K)
      (p₀ : Polynomial (MvPolynomial (Fin n) (CoefficientSystem.Constructions.Foundations.coefficientRing R K s)))
      (d₀ : MvPolynomial (Fin n) (CoefficientSystem.Constructions.Foundations.coefficientRing R K s)),
      Polynomial.map (MvPolynomial.map (algebraMap (CoefficientSystem.Constructions.Foundations.coefficientRing R K s) K)) p₀ = p ∧
      MvPolynomial.map (algebraMap (CoefficientSystem.Constructions.Foundations.coefficientRing R K s) K) d₀ = d ∧
      p₀.Monic ∧ p₀.natDegree = p.natDegree := by
  classical
  let q := (MvPolynomial.finSuccEquiv K n).symm p
  let s := q.coeffs ∪ d.coeffs
  let A := CoefficientSystem.Constructions.Foundations.coefficientRing R K s
  let φ : A →+* K := algebraMap A K
  have hq : q ∈ Set.range (MvPolynomial.map φ) := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro x hx
    exact ⟨⟨x, Algebra.subset_adjoin (Finset.mem_union_left _ hx)⟩, rfl⟩
  have hd : d ∈ Set.range (MvPolynomial.map φ) := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro x hx
    exact ⟨⟨x, Algebra.subset_adjoin (Finset.mem_union_right _ hx)⟩, rfl⟩
  obtain ⟨q₀, hq₀⟩ := hq
  obtain ⟨d₀, hd₀⟩ := hd
  let p₀ := MvPolynomial.finSuccEquiv A n q₀
  have hmap : Polynomial.map (MvPolynomial.map φ) p₀ = p := by
    rw [← PolynomialCoordinates.Construction.finSuccEquiv_map, hq₀]
    exact (MvPolynomial.finSuccEquiv K n).apply_symm_apply p
  have hm : p₀.Monic := Polynomial.monic_of_injective
    (MvPolynomial.map_injective φ Subtype.val_injective) (hmap ▸ hp)
  refine ⟨s, p₀, d₀, hmap, hd₀, hm, ?_⟩
  rw [← hmap, hm.natDegree_map]

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.HypersurfaceCoefficients.Construction
