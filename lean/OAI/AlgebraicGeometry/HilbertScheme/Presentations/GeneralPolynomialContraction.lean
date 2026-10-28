import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CechHomotopy

/-! # General Polynomial Contraction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.GeneralPolynomialContraction.ProjectiveCech

noncomputable section

/-! A polynomial Čech contraction in every internal degree, away from the monomials whose exponents are all negative. -/

universe u v

variable {σ : Type u} [Fintype σ] [LinearOrder σ] [Nonempty σ]
variable (R : Type v) [CommRing R]

def generalCechPivot (a : σ → ℤ) : σ :=
  if h : ∃ i, 0 ≤ a i then h.choose else Classical.arbitrary σ

omit [LinearOrder σ] in
theorem generalCechPivot_nonnegative (a : σ → ℤ) (h : ∃ i, 0 ≤ a i) :
    0 ≤ a (generalCechPivot a) := by
  simp only [generalCechPivot, dite_eq_left h]
  exact h.choose_spec

def generalContractionCoefficient (f : Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (s : Finset σ) (a : σ → ℤ) : R :=
  if ∃ i, 0 ≤ a i then Cech.Contraction.ProjectiveCech.cechContraction R (generalCechPivot a)
    (fun t => LaurentCoordinates.ProjectiveCech.chartCoordinates R t (f t) a) s else 0

theorem generalContractionCoefficient_support (f : Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (s : Finset σ) (a : σ → ℤ) (ha : generalContractionCoefficient R f s a ≠ 0) :
    a ∈ Polynomial.CechHomotopy.ProjectiveCech.polynomialCechSupport R f := by
  have hne : LaurentCoordinates.ProjectiveCech.chartCoordinates R (insert (generalCechPivot a) s) (f (insert (generalCechPivot a) s)) a ≠ 0 := by
    intro hz
    exact ha (by simp only [generalContractionCoefficient, Cech.Contraction.ProjectiveCech.cechContraction, hz, mul_zero, ite_self])
  exact Polynomial.CechHomotopy.ProjectiveCech.mem_polynomialCechSupport R f _ a hne

def generalContractionCoefficients (f : Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (s : Finset σ) : (σ → ℤ) →₀ R :=
  Finsupp.onFinset (Polynomial.CechHomotopy.ProjectiveCech.polynomialCechSupport R f) (generalContractionCoefficient R f s)
    (generalContractionCoefficient_support R f s)

theorem generalContractionCoefficients_apply (f : Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (s : Finset σ) (a : σ → ℤ) :
    generalContractionCoefficients R f s a = generalContractionCoefficient R f s a := rfl

theorem generalContractionCoefficients_allowed (f : Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) (s : Finset σ) :
    ∀ a ∈ (generalContractionCoefficients R f s).support, a ∈ LaurentCoordinates.ProjectiveCech.allowedExponents s := by
  intro a ha
  have hne := Finsupp.mem_support_iff.mp ha
  have hex : ∃ i, 0 ≤ a i := by
    by_contra hn
    exact hne (by simp only [generalContractionCoefficients_apply, generalContractionCoefficient, ite_eq_right hn])
  have hj : generalCechPivot a ∉ LaurentDegree.ProjectiveCech.negativeSupport a := by
    intro h
    exact (not_lt_of_ge (generalCechPivot_nonnegative a hex)) (Finset.mem_filter.mp h).2
  by_contra hallowed
  apply hne
  rw [generalContractionCoefficients_apply, generalContractionCoefficient, ite_eq_left hex]
  apply Cech.Contraction.ProjectiveCech.cechContraction_preserves_support R (generalCechPivot a) (LaurentDegree.ProjectiveCech.negativeSupport a) hj
    (fun t => LaurentCoordinates.ProjectiveCech.chartCoordinates R t (f t) a) ?_ s ?_
  · intro t ht
    exact LaurentCoordinates.ProjectiveCech.chartCoordinates_of_not_allowed R t (f t) a
      (fun h => ht ((LaurentDegree.ProjectiveCech.negativeSupport_subset_iff a t).mpr h))
  · exact fun h => hallowed ((LaurentDegree.ProjectiveCech.negativeSupport_subset_iff a s).mp h)

def generalPolynomialCechContraction (f : Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) :
    Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R :=
  fun s => LaurentCoordinates.ProjectiveCech.chartOfCoordinates R s (generalContractionCoefficients R f s)

theorem generalPolynomialCechContraction_coordinates (f : Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (s : Finset σ) (a : σ → ℤ) :
    LaurentCoordinates.ProjectiveCech.chartCoordinates R s (generalPolynomialCechContraction R f s) a =
      generalContractionCoefficient R f s a := by
  rw [generalPolynomialCechContraction, LaurentCoordinates.ProjectiveCech.chartCoordinates_ofCoordinates R s _
    (generalContractionCoefficients_allowed R f s)]
  rfl

theorem generalPolynomialCechContraction_homogeneous (d : ℤ) (f : Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (hf : Polynomial.Cech.ProjectiveCech.CechHomogeneous R d f) : Polynomial.Cech.ProjectiveCech.CechHomogeneous R d (generalPolynomialCechContraction R f) := by
  intro s
  apply LaurentCoordinates.ProjectiveCech.chartOfCoordinates_degree R s d
  intro a ha
  have hc := LaurentCoordinates.ProjectiveCech.chartCoordinates_degree R (insert (generalCechPivot a) s) d _ (hf _) a ha
  simp only [generalContractionCoefficients_apply, generalContractionCoefficient, Cech.Contraction.ProjectiveCech.cechContraction,
    hc, mul_zero, ite_self]

theorem generalPolynomialCechContraction_card (q : ℕ) (f : Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (hf : Polynomial.Cech.ProjectiveCech.CechCardSupported R (q + 1) f) : Polynomial.Cech.ProjectiveCech.CechCardSupported R q (generalPolynomialCechContraction R f) := by
  intro s hs
  have hz : generalContractionCoefficients R f s = 0 := by
    ext a
    rw [generalContractionCoefficients_apply, Finsupp.zero_apply, generalContractionCoefficient]
    split_ifs
    · apply Cech.Contraction.ProjectiveCech.cechContraction_card_support R (generalCechPivot a) q _ ?_ s hs
      intro t ht
      rw [hf t ht, map_zero, Finsupp.zero_apply]
    · rfl
  change LaurentCoordinates.ProjectiveCech.chartOfCoordinates R s _ = 0
  rw [hz, map_zero]

theorem generalPolynomialCechContraction_zero :
    generalPolynomialCechContraction R (0 : Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) = 0 := by
  funext s
  have hz : generalContractionCoefficients R (0 : Polynomial.Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) s = 0 := by
    ext a
    simp only [generalContractionCoefficients_apply, generalContractionCoefficient, Pi.zero_apply,
      map_zero, Finsupp.zero_apply, Cech.Contraction.ProjectiveCech.cechContraction, mul_zero, ite_self]
  change LaurentCoordinates.ProjectiveCech.chartOfCoordinates R s _ = 0
  rw [hz, map_zero]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.GeneralPolynomialContraction.ProjectiveCech
