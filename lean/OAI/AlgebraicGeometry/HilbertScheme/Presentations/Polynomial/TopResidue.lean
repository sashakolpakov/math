import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GeneralPolynomialContraction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.NegativeDegree

/-! # Top Residue -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.TopResidue.ProjectiveCech

noncomputable section

/-! The all-negative Laurent part of an actual polynomial Čech cochain is supported on the final intersection. -/

universe u v

variable {σ : Type u} [Fintype σ] [LinearOrder σ]
variable (R : Type v) [CommRing R]

def polynomialTopResidueCoefficients (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (s : Finset σ) : (σ → ℤ) →₀ R :=
  (LaurentCoordinates.ProjectiveCech.chartCoordinates R s (f s)).filter (fun a => ¬∃ i, 0 ≤ a i)

theorem polynomialTopResidueCoefficients_apply (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (s : Finset σ) (a : σ → ℤ) :
    polynomialTopResidueCoefficients R f s a =
      if ∃ i, 0 ≤ a i then 0 else LaurentCoordinates.ProjectiveCech.chartCoordinates R s (f s) a := by
  simp only [polynomialTopResidueCoefficients, Finsupp.filter_apply, ite_not]

theorem polynomialTopResidueCoefficients_allowed (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) (s : Finset σ) :
    ∀ a ∈ (polynomialTopResidueCoefficients R f s).support, a ∈ LaurentCoordinates.ProjectiveCech.allowedExponents s := by
  intro a ha
  exact LaurentCoordinates.ProjectiveCech.chartCoordinates_support R s (f s) a (Finset.mem_filter.mp ha).1

def polynomialTopResidue (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R :=
  fun s => LaurentCoordinates.ProjectiveCech.chartOfCoordinates R s (polynomialTopResidueCoefficients R f s)

theorem polynomialTopResidue_coordinates (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (s : Finset σ) (a : σ → ℤ) :
    LaurentCoordinates.ProjectiveCech.chartCoordinates R s (polynomialTopResidue R f s) a =
      if ∃ i, 0 ≤ a i then 0 else LaurentCoordinates.ProjectiveCech.chartCoordinates R s (f s) a := by
  rw [polynomialTopResidue, LaurentCoordinates.ProjectiveCech.chartCoordinates_ofCoordinates R s _
    (polynomialTopResidueCoefficients_allowed R f s)]
  exact polynomialTopResidueCoefficients_apply R f s a

theorem polynomialTopResidue_homogeneous (d : ℤ) (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (hf : Cech.ProjectiveCech.CechHomogeneous R d f) : Cech.ProjectiveCech.CechHomogeneous R d (polynomialTopResidue R f) := by
  intro s
  apply LaurentCoordinates.ProjectiveCech.chartOfCoordinates_degree R s d
  intro a ha
  rw [polynomialTopResidueCoefficients_apply, LaurentCoordinates.ProjectiveCech.chartCoordinates_degree R s d _ (hf s) a ha]
  simp only [ite_self]

theorem polynomialTopResidue_of_not_univ (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (s : Finset σ) (hs : s ≠ Finset.univ) : polynomialTopResidue R f s = 0 := by
  apply LaurentCoordinates.ProjectiveCech.chartCoordinates_injective R s
  ext a
  rw [polynomialTopResidue_coordinates, map_zero, Finsupp.zero_apply]
  split_ifs with ha
  · rfl
  · apply LaurentCoordinates.ProjectiveCech.chartCoordinates_of_not_allowed
    intro hallowed
    apply hs
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    by_contra hi
    exact ha ⟨i, hallowed i hi⟩

theorem polynomialTopResidue_card (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) :
    Cech.ProjectiveCech.CechCardSupported R (Fintype.card σ) (polynomialTopResidue R f) := by
  intro s hs
  apply polynomialTopResidue_of_not_univ R f s
  intro h
  exact hs (h ▸ Finset.card_univ)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.TopResidue.ProjectiveCech
