import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.TopResidue

/-! # Cech Residue Identity -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CechResidueIdentity.ProjectiveCech

noncomputable section

/-! In every internal degree, the polynomial Čech homotopy leaves precisely the all-negative top Laurent part. -/

universe u v

variable {σ : Type u} [Fintype σ] [LinearOrder σ] [Nonempty σ]
variable (R : Type v) [CommRing R]

theorem polynomialCech_general_contraction_identity (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) :
    Cech.ProjectiveCech.polynomialCechDifferential R (GeneralPolynomialContraction.ProjectiveCech.generalPolynomialCechContraction R f) +
      GeneralPolynomialContraction.ProjectiveCech.generalPolynomialCechContraction R (Cech.ProjectiveCech.polynomialCechDifferential R f) =
        f - TopResidue.ProjectiveCech.polynomialTopResidue R f := by
  funext s
  apply LaurentCoordinates.ProjectiveCech.chartCoordinates_injective R s
  ext a
  change LaurentCoordinates.ProjectiveCech.chartCoordinates R s (Cech.ProjectiveCech.polynomialCechDifferential R (GeneralPolynomialContraction.ProjectiveCech.generalPolynomialCechContraction R f) s +
    GeneralPolynomialContraction.ProjectiveCech.generalPolynomialCechContraction R (Cech.ProjectiveCech.polynomialCechDifferential R f) s) a =
      LaurentCoordinates.ProjectiveCech.chartCoordinates R s (f s - TopResidue.ProjectiveCech.polynomialTopResidue R f s) a
  rw [map_add, Finsupp.add_apply, map_sub, Finsupp.sub_apply, Cech.ProjectiveCech.polynomialCechDifferential_coordinates,
    GeneralPolynomialContraction.ProjectiveCech.generalPolynomialCechContraction_coordinates, TopResidue.ProjectiveCech.polynomialTopResidue_coordinates]
  by_cases ha : ∃ i, 0 ≤ a i
  · have hH : (fun t => LaurentCoordinates.ProjectiveCech.chartCoordinates R t (GeneralPolynomialContraction.ProjectiveCech.generalPolynomialCechContraction R f t) a) =
        Cech.Contraction.ProjectiveCech.cechContraction R (GeneralPolynomialContraction.ProjectiveCech.generalCechPivot a) (fun t => LaurentCoordinates.ProjectiveCech.chartCoordinates R t (f t) a) := by
      funext t
      rw [GeneralPolynomialContraction.ProjectiveCech.generalPolynomialCechContraction_coordinates, GeneralPolynomialContraction.ProjectiveCech.generalContractionCoefficient, ite_eq_left ha]
    have hD : (fun t => LaurentCoordinates.ProjectiveCech.chartCoordinates R t (Cech.ProjectiveCech.polynomialCechDifferential R f t) a) =
        Cech.Contraction.ProjectiveCech.cechDifferential R (fun t => LaurentCoordinates.ProjectiveCech.chartCoordinates R t (f t) a) := by
      funext t
      exact Cech.ProjectiveCech.polynomialCechDifferential_coordinates R f t a
    rw [hH, GeneralPolynomialContraction.ProjectiveCech.generalContractionCoefficient]
    simp only [ite_eq_left ha, hD, sub_zero]
    exact Cech.Contraction.ProjectiveCech.cech_contraction_identity R (GeneralPolynomialContraction.ProjectiveCech.generalCechPivot a) _ s
  · have hH : (fun t => LaurentCoordinates.ProjectiveCech.chartCoordinates R t (GeneralPolynomialContraction.ProjectiveCech.generalPolynomialCechContraction R f t) a) = 0 := by
      funext t
      rw [GeneralPolynomialContraction.ProjectiveCech.generalPolynomialCechContraction_coordinates, GeneralPolynomialContraction.ProjectiveCech.generalContractionCoefficient, ite_eq_right ha]
      rfl
    rw [hH, GeneralPolynomialContraction.ProjectiveCech.generalContractionCoefficient]
    simp only [ite_eq_right ha, sub_self, add_zero, Cech.Contraction.ProjectiveCech.cechDifferential, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

theorem polynomialCech_cycle_mod_top_residue (d : ℤ) (q : ℕ)
    (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) (hf : Cech.ProjectiveCech.CechHomogeneous R d f)
    (hcard : Cech.ProjectiveCech.CechCardSupported R (q + 1) f) (hcycle : Cech.ProjectiveCech.polynomialCechDifferential R f = 0) :
    ∃ g : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R,
      Cech.ProjectiveCech.CechHomogeneous R d g ∧ Cech.ProjectiveCech.CechCardSupported R q g ∧
        Cech.ProjectiveCech.polynomialCechDifferential R g = f - TopResidue.ProjectiveCech.polynomialTopResidue R f := by
  refine ⟨GeneralPolynomialContraction.ProjectiveCech.generalPolynomialCechContraction R f, GeneralPolynomialContraction.ProjectiveCech.generalPolynomialCechContraction_homogeneous R d f hf,
    GeneralPolynomialContraction.ProjectiveCech.generalPolynomialCechContraction_card R q f hcard, ?_⟩
  have h := polynomialCech_general_contraction_identity R f
  rwa [hcycle, GeneralPolynomialContraction.ProjectiveCech.generalPolynomialCechContraction_zero, add_zero] at h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CechResidueIdentity.ProjectiveCech
