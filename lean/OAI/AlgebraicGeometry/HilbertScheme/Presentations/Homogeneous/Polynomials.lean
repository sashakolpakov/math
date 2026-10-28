import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GroebnerGenerators
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.MonomialBasis

/-! # Polynomials -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.Polynomials.GradedHilbert

noncomputable section

/-! Critical-pair polynomials are homogeneous and their total degrees are controlled by the input generator degrees. -/

open _root_.MvPolynomial

universe u

variable {K : Type u} [Field K] {n : ℕ}
variable (m : MonomialOrder (Fin (n + 1)))

theorem homogeneous_leadingDegree {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n} {d : ℕ}
    (hf : f.IsHomogeneous d) (hf0 : f ≠ 0) : (m.degree f).degree = d :=
  (Hilbert.MonomialBasis.GradedHilbert.mem_degreeSpace_iff_support f d).mp hf (m.degree f) (m.degree_mem_support hf0)

theorem sPolynomial_homogeneous {f g : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n} {d e : ℕ}
    (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous e) (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    (m.sPolynomial f g).IsHomogeneous (m.degree f ⊔ m.degree g).degree := by
  have hdf := homogeneous_leadingDegree m hf hf0
  have hdg := homogeneous_leadingDegree m hg hg0
  have hleft : (m.degree f ⊔ m.degree g - m.degree f).degree + d =
      (m.degree f ⊔ m.degree g).degree := by
    rw [← hdf, ← map_add, tsub_add_cancel_of_le le_sup_left]
  have hright : (m.degree f ⊔ m.degree g - m.degree g).degree + e =
      (m.degree f ⊔ m.degree g).degree := by
    rw [← hdg, ← map_add, tsub_add_cancel_of_le le_sup_right]
  rw [MonomialOrder.sPolynomial_def]
  apply IsHomogeneous.sub
  · have h := (isHomogeneous_monomial (m.leadingCoeff g)
      (rfl : (m.degree f ⊔ m.degree g - m.degree f).degree = _)).mul hf
    simpa only [hleft] using h
  · have h := (isHomogeneous_monomial (m.leadingCoeff f)
      (rfl : (m.degree f ⊔ m.degree g - m.degree g).degree = _)).mul hg
    simpa only [hright] using h

theorem sPolynomial_total_degree_bound {f g : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n} {d e : ℕ}
    (hf : f.IsHomogeneous d) (hg : g.IsHomogeneous e) (hf0 : f ≠ 0) (hg0 : g ≠ 0) :
    (m.degree f ⊔ m.degree g).degree ≤ d + e := by
  rw [← homogeneous_leadingDegree m hf hf0, ← homogeneous_leadingDegree m hg hg0, ← map_add]
  apply Finsupp.degree_mono
  exact sup_le (le_add_right le_rfl) (le_add_left le_rfl)

theorem sPolynomial_mem_ideal {I : Ideal (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)} {f g : Hilbert.Polynomial.GradedHilbert.CoordinateRing K n}
    (hf : f ∈ I) (hg : g ∈ I) : m.sPolynomial f g ∈ I := by
  rw [MonomialOrder.sPolynomial_def]
  exact I.sub_mem (I.mul_mem_left _ hf) (I.mul_mem_left _ hg)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.Polynomials.GradedHilbert
