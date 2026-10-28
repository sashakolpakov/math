import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Cech

/-! # Cech Homotopy -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CechHomotopy.ProjectiveCech

noncomputable section

/-!
The exponentwise contraction is finitely supported and defines actual
elements of the homogeneous chart localizations in nonnegative degree.
-/

universe u v

variable {σ : Type u} [Fintype σ] [LinearOrder σ] [Nonempty σ]
variable (R : Type v) [CommRing R]

def cechPivot (a : σ → ℤ) : σ :=
  if ha : 0 ≤ LaurentDegree.ProjectiveCech.exponentDegree a then (LaurentDegree.ProjectiveCech.exists_outside_negativeSupport a ha).choose
  else Classical.arbitrary σ

omit [LinearOrder σ] in
theorem cechPivot_not_negative (a : σ → ℤ) (ha : 0 ≤ LaurentDegree.ProjectiveCech.exponentDegree a) :
    cechPivot a ∉ LaurentDegree.ProjectiveCech.negativeSupport a := by
  simp only [cechPivot, dite_eq_left ha]
  exact (LaurentDegree.ProjectiveCech.exists_outside_negativeSupport a ha).choose_spec

def polynomialCechSupport (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) : Finset (σ → ℤ) :=
  Finset.univ.biUnion (fun s : Finset σ => (LaurentCoordinates.ProjectiveCech.chartCoordinates R s (f s)).support)

omit [Nonempty σ] in
theorem mem_polynomialCechSupport (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (s : Finset σ) (a : σ → ℤ) (ha : LaurentCoordinates.ProjectiveCech.chartCoordinates R s (f s) a ≠ 0) :
    a ∈ polynomialCechSupport R f :=
  Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, Finsupp.mem_support_iff.mpr ha⟩

def polynomialContractionCoefficients (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (s : Finset σ) : (σ → ℤ) →₀ R :=
  Finsupp.onFinset (polynomialCechSupport R f)
    (fun a => Cech.Contraction.ProjectiveCech.cechContraction R (cechPivot a) (fun t => LaurentCoordinates.ProjectiveCech.chartCoordinates R t (f t) a) s)
    (by
      intro a ha
      have hc : LaurentCoordinates.ProjectiveCech.chartCoordinates R (insert (cechPivot a) s) (f (insert (cechPivot a) s)) a ≠ 0 := by
        intro hz
        exact ha (by simp only [Cech.Contraction.ProjectiveCech.cechContraction, hz, mul_zero, ite_self])
      exact mem_polynomialCechSupport R f _ a hc)

theorem polynomialContractionCoefficients_apply (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (s : Finset σ) (a : σ → ℤ) :
    polynomialContractionCoefficients R f s a =
      Cech.Contraction.ProjectiveCech.cechContraction R (cechPivot a) (fun t => LaurentCoordinates.ProjectiveCech.chartCoordinates R t (f t) a) s := rfl

theorem polynomialContractionCoefficients_degree (d : ℤ) (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (hf : Cech.ProjectiveCech.CechHomogeneous R d f) (s : Finset σ) (a : σ → ℤ) (ha : LaurentDegree.ProjectiveCech.exponentDegree a ≠ d) :
    polynomialContractionCoefficients R f s a = 0 := by
  rw [polynomialContractionCoefficients_apply]
  have hc := LaurentCoordinates.ProjectiveCech.chartCoordinates_degree R (insert (cechPivot a) s) d _ (hf _) a ha
  simp only [Cech.Contraction.ProjectiveCech.cechContraction, hc, mul_zero, ite_self]

theorem polynomialContractionCoefficients_allowed (d : ℤ) (hd : 0 ≤ d)
    (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) (hf : Cech.ProjectiveCech.CechHomogeneous R d f) (s : Finset σ) :
    ∀ a ∈ (polynomialContractionCoefficients R f s).support, a ∈ LaurentCoordinates.ProjectiveCech.allowedExponents s := by
  intro a ha
  have hne := Finsupp.mem_support_iff.mp ha
  have hdeg : LaurentDegree.ProjectiveCech.exponentDegree a = d := by
    by_contra hn
    exact hne (polynomialContractionCoefficients_degree R d f hf s a hn)
  have hj : cechPivot a ∉ LaurentDegree.ProjectiveCech.negativeSupport a := cechPivot_not_negative a (hdeg ▸ hd)
  by_contra hallowed
  apply hne
  rw [polynomialContractionCoefficients_apply]
  apply Cech.Contraction.ProjectiveCech.cechContraction_preserves_support R (cechPivot a) (LaurentDegree.ProjectiveCech.negativeSupport a) hj
    (fun t => LaurentCoordinates.ProjectiveCech.chartCoordinates R t (f t) a) ?_ s ?_
  · intro t ht
    exact LaurentCoordinates.ProjectiveCech.chartCoordinates_of_not_allowed R t (f t) a
      (fun h => ht ((LaurentDegree.ProjectiveCech.negativeSupport_subset_iff a t).mpr h))
  · exact fun h => hallowed ((LaurentDegree.ProjectiveCech.negativeSupport_subset_iff a s).mp h)

def polynomialCechContraction (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) :
    Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R :=
  fun s => LaurentCoordinates.ProjectiveCech.chartOfCoordinates R s (polynomialContractionCoefficients R f s)

theorem polynomialCechContraction_coordinates (d : ℤ) (hd : 0 ≤ d)
    (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R) (hf : Cech.ProjectiveCech.CechHomogeneous R d f)
    (s : Finset σ) (a : σ → ℤ) :
    LaurentCoordinates.ProjectiveCech.chartCoordinates R s (polynomialCechContraction R f s) a =
      Cech.Contraction.ProjectiveCech.cechContraction R (cechPivot a) (fun t => LaurentCoordinates.ProjectiveCech.chartCoordinates R t (f t) a) s := by
  rw [polynomialCechContraction, LaurentCoordinates.ProjectiveCech.chartCoordinates_ofCoordinates R s _
    (polynomialContractionCoefficients_allowed R d hd f hf s)]
  rfl

theorem polynomialCechContraction_homogeneous (d : ℤ) (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (hf : Cech.ProjectiveCech.CechHomogeneous R d f) : Cech.ProjectiveCech.CechHomogeneous R d (polynomialCechContraction R f) := by
  intro s
  exact LaurentCoordinates.ProjectiveCech.chartOfCoordinates_degree R s d _ (polynomialContractionCoefficients_degree R d f hf s)

theorem polynomialCechContraction_card (q : ℕ) (f : Cech.ProjectiveCech.PolynomialCechFamily (σ := σ) R)
    (hf : Cech.ProjectiveCech.CechCardSupported R (q + 1) f) : Cech.ProjectiveCech.CechCardSupported R q (polynomialCechContraction R f) := by
  intro s hs
  have hz : polynomialContractionCoefficients R f s = 0 := by
    ext a
    rw [polynomialContractionCoefficients_apply, Finsupp.zero_apply]
    apply Cech.Contraction.ProjectiveCech.cechContraction_card_support R (cechPivot a) q _ ?_ s hs
    intro t ht
    rw [hf t ht, map_zero, Finsupp.zero_apply]
  change LaurentCoordinates.ProjectiveCech.chartOfCoordinates R s (polynomialContractionCoefficients R f s) = 0
  rw [hz, map_zero]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.CechHomotopy.ProjectiveCech
