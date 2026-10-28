import OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceCoefficientTransform

/-! # Controlled Generator Family -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ControlledGeneratorFamily.Construction

noncomputable section

/-! Fixed generating families on successive actual controlled transforms. -/

variable {R S ι : Type*} [CommRing R] [CommRing S]

/-- Dividing a fixed family by a regular common factor gives generators of
the actual ideal quotient; all sections of the ideal need not be re-indexed. -/
theorem span_map_colon_eq_span_of_factor (φ : R →+* S) (p : ι → R) (q : ι → S)
    (c : S) (hc : IsRegular c) (h : ∀ t, φ (p t) = c * q t) :
    ((Ideal.span (Set.range p)).map φ).colon (Ideal.span {c}) = Ideal.span (Set.range q) := by
  rw [Ideal.map_span, ← Set.range_comp]
  have he : φ ∘ p = fun t => c * q t := funext h
  rw [he, ResidualCoefficientTransform.Construction.span_range_mul_left, ResidualCoefficientTransform.Construction.colon_principal_mul_of_regular _ _ hc]

/-- The next family retains its original index set and consists of the
uniquely divided original generators on the actual Rees chart. -/
def blowupChartTransformFamily (I : Ideal R) (p : ι → R) (a : I) (b : ℕ)
    (hp : Ideal.span (Set.range p) ≤ I ^ b) : ι → Blowup.Charts.Construction.blowupChart I a :=
  fun t => Coordinate.BlowupTransform.Construction.blowupChartTransformSection I (Ideal.span (Set.range p)) a b hp
    ⟨p t, Ideal.subset_span ⟨t, rfl⟩⟩

theorem blowupChartTransformFamily_spec (I : Ideal R) (p : ι → R) (a : I) (b : ℕ)
    (hp : Ideal.span (Set.range p) ≤ I ^ b) (t : ι) :
    Blowup.Charts.Construction.blowupChartConstants I a (p t) = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ b *
      blowupChartTransformFamily I p a b hp t :=
  Coordinate.BlowupTransform.Construction.blowupChartTransformSection_spec I (Ideal.span (Set.range p)) a b hp
    ⟨p t, Ideal.subset_span ⟨t, rfl⟩⟩

/-- The transformed fixed family generates precisely the controlled ideal. -/
theorem blowupControlledTransform_eq_span_family (I : Ideal R) (p : ι → R) (a : I) (b : ℕ)
    (hp : Ideal.span (Set.range p) ≤ I ^ b) :
    ControlledTransform.Construction.blowupControlledTransform I (Ideal.span (Set.range p)) b a =
      Ideal.span (Set.range (blowupChartTransformFamily I p a b hp)) :=
  span_map_colon_eq_span_of_factor (Blowup.Charts.Construction.blowupChartConstants I a) p _ _
    (IsRegular.pow (a := Blowup.Charts.Construction.blowupChartConstants I a a.val) b
      (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a))
    (blowupChartTransformFamily_spec I p a b hp)

/-- Differential coefficient families have the exact exceptional factors
for any fixed generator family and any chosen divisions satisfying the equation. -/
theorem coordinateDerivativeFamilyIdeal_blowup_factorization
    (I : Ideal R) (a z : I) (D : Derivation ℤ R R) (ha : D a.val = 0)
    (p : ι → R) (q : ι → Blowup.Charts.Construction.blowupChart I a) (b j : ℕ) (hj : j ≤ b)
    (h : ∀ t, Blowup.Charts.Construction.blowupChartConstants I a (p t) = Blowup.Charts.Construction.blowupChartConstants I a a.val ^ b * q t) :
    (HypersurfaceCoefficientTransform.Construction.coordinateDerivativeFamilyIdeal D z.val p j).map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z) =
      Ideal.span {(Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
        (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ^ (b - j)} *
      HypersurfaceCoefficientTransform.Construction.coordinateDerivativeFamilyIdeal (ChartDerivation.Construction.blowupChartDerivation I a D) (ExceptionalIdeal.Construction.blowupChartRatio I a z) q j := by
  rw [HypersurfaceCoefficientTransform.Construction.coordinateDerivativeFamilyIdeal, Ideal.map_span, ← Set.range_comp]
  have he : (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z ∘
      fun t => Ideal.Quotient.mk (Ideal.span {z.val}) (D^[j] (p t))) =
      fun t => (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
        (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ^ (b - j) *
        Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
          ((ChartDerivation.Construction.blowupChartDerivation I a D)^[j] (q t)) := by
    funext t
    rw [Function.comp_apply, HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap_mk]
    have hd := Coordinate.BlowupTransform.Construction.blowupChart_iteratedCoordinateDerivation_division I a D ha (b - j) j (p t) (q t)
      (by simpa only [Nat.sub_add_cancel hj] using h t)
    rw [hd, map_mul, map_pow (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z}))]
  rw [he, ResidualCoefficientTransform.Construction.span_range_mul_left]
  rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ControlledGeneratorFamily.Construction
