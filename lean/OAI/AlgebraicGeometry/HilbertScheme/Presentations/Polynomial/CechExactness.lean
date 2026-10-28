import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CechHomotopy

/-! # Cech Exactness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CechExactness.ProjectiveCech

noncomputable section

/-! Exactness in nonnegative degrees of the augmented polynomial Čech complex. -/

universe u v

variable {σ : Type u} [Fintype σ] [LinearOrder σ] [Nonempty σ]
variable (R : Type v) [CommRing R]

theorem polynomialCech_contraction_identity (d : ℤ) (hd : 0 ≤ d)
    (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) (hf : Cech.ProjectiveCech.CechHomogeneous R d f) :
    Cech.ProjectiveCech.polynomialCechDifferential R (CechHomotopy.ProjectiveCech.polynomialCechContraction R f) +
      CechHomotopy.ProjectiveCech.polynomialCechContraction R (Cech.ProjectiveCech.polynomialCechDifferential R f) = f := by
  funext s
  apply LaurentCoordinates.ProjectiveCech.chartCoordinates_injective R s
  ext a
  change LaurentCoordinates.ProjectiveCech.chartCoordinates R s (Cech.ProjectiveCech.polynomialCechDifferential R (CechHomotopy.ProjectiveCech.polynomialCechContraction R f) s +
    CechHomotopy.ProjectiveCech.polynomialCechContraction R (Cech.ProjectiveCech.polynomialCechDifferential R f) s) a = _
  rw [map_add, Finsupp.add_apply, Cech.ProjectiveCech.polynomialCechDifferential_coordinates,
    CechHomotopy.ProjectiveCech.polynomialCechContraction_coordinates R d hd _ (Cech.ProjectiveCech.polynomialCechDifferential_homogeneous R d f hf)]
  have hH : (fun t => LaurentCoordinates.ProjectiveCech.chartCoordinates R t (CechHomotopy.ProjectiveCech.polynomialCechContraction R f t) a) =
      Cech.Contraction.ProjectiveCech.cechContraction R (CechHomotopy.ProjectiveCech.cechPivot a) (fun t => LaurentCoordinates.ProjectiveCech.chartCoordinates R t (f t) a) := by
    funext t
    exact CechHomotopy.ProjectiveCech.polynomialCechContraction_coordinates R d hd f hf t a
  have hD : (fun t => LaurentCoordinates.ProjectiveCech.chartCoordinates R t (Cech.ProjectiveCech.polynomialCechDifferential R f t) a) =
      Cech.Contraction.ProjectiveCech.cechDifferential R (fun t => LaurentCoordinates.ProjectiveCech.chartCoordinates R t (f t) a) := by
    funext t
    exact Cech.ProjectiveCech.polynomialCechDifferential_coordinates R f t a
  rw [hH, hD]
  exact Cech.Contraction.ProjectiveCech.cech_contraction_identity R (CechHomotopy.ProjectiveCech.cechPivot a) _ s

theorem polynomialCechContraction_zero :
    CechHomotopy.ProjectiveCech.polynomialCechContraction R (0 : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) = 0 := by
  funext s
  have h : CechHomotopy.ProjectiveCech.polynomialContractionCoefficients R (0 : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) s = 0 := by
    ext a
    simp only [CechHomotopy.ProjectiveCech.polynomialContractionCoefficients_apply, Pi.zero_apply, map_zero,
      Finsupp.zero_apply, Cech.Contraction.ProjectiveCech.cechContraction, mul_zero, ite_self]
  change LaurentCoordinates.ProjectiveCech.chartOfCoordinates R s _ = 0
  rw [h, map_zero]

theorem polynomialCech_exact (d : ℤ) (hd : 0 ≤ d) (q : ℕ)
    (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) (hf : Cech.ProjectiveCech.CechHomogeneous R d f)
    (hcard : Cech.ProjectiveCech.CechCardSupported R (q + 1) f) (hcocycle : Cech.ProjectiveCech.polynomialCechDifferential R f = 0) :
    ∃ g : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R,
      Cech.ProjectiveCech.CechHomogeneous R d g ∧ Cech.ProjectiveCech.CechCardSupported R q g ∧ Cech.ProjectiveCech.polynomialCechDifferential R g = f := by
  refine ⟨CechHomotopy.ProjectiveCech.polynomialCechContraction R f, CechHomotopy.ProjectiveCech.polynomialCechContraction_homogeneous R d f hf,
    CechHomotopy.ProjectiveCech.polynomialCechContraction_card R q f hcard, ?_⟩
  have h := polynomialCech_contraction_identity R d hd f hf
  rwa [hcocycle, polynomialCechContraction_zero, add_zero] at h

theorem polynomialCechContraction_card_zero (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (hf : Cech.ProjectiveCech.CechCardSupported R 0 f) : CechHomotopy.ProjectiveCech.polynomialCechContraction R f = 0 := by
  funext s
  have h : CechHomotopy.ProjectiveCech.polynomialContractionCoefficients R f s = 0 := by
    ext a
    rw [CechHomotopy.ProjectiveCech.polynomialContractionCoefficients_apply, Finsupp.zero_apply]
    have hi : (insert (CechHomotopy.ProjectiveCech.cechPivot a) s).card ≠ 0 :=
      Finset.card_ne_zero.mpr ⟨CechHomotopy.ProjectiveCech.cechPivot a, Finset.mem_insert_self _ _⟩
    simp only [Cech.Contraction.ProjectiveCech.cechContraction, hf _ hi, map_zero, Finsupp.zero_apply, mul_zero, ite_self]
  change LaurentCoordinates.ProjectiveCech.chartOfCoordinates R s _ = 0
  rw [h, map_zero]

theorem polynomialCech_augmentation_injective (d : ℤ) (hd : 0 ≤ d)
    (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) (hf : Cech.ProjectiveCech.CechHomogeneous R d f)
    (hcard : Cech.ProjectiveCech.CechCardSupported R 0 f) (hcocycle : Cech.ProjectiveCech.polynomialCechDifferential R f = 0) : f = 0 := by
  have h := polynomialCech_contraction_identity R d hd f hf
  rw [polynomialCechContraction_card_zero R f hcard, map_zero, hcocycle,
    polynomialCechContraction_zero, add_zero] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CechExactness.ProjectiveCech
