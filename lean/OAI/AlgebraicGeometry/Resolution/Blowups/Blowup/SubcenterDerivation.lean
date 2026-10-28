import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.SubcenterMap
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BlowupTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup

/-! # Subcenter Derivation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.SubcenterDerivation.Construction

noncomputable section

/-! A normal derivation continues to fix the transformed hypersurface chart. -/

universe u

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Clearing denominators shows that a derivation vanishing on the base
also vanishes on an embedded blowup chart with regular exceptional parameter. -/
theorem derivation_zero_on_blowupChart_image {k : Type*} [CommRing k] [Algebra k S]
    (I : Ideal R) (a : I) (f : Charts.Construction.blowupChart I a →+* S) (D : Derivation k S S)
    (hc : IsRegular (f (Charts.Construction.blowupChartConstants I a a.val)))
    (hD : ∀ r : R, D (f (Charts.Construction.blowupChartConstants I a r)) = 0) :
    ∀ x : Charts.Construction.blowupChart I a, D (f x) = 0 := by
  intro x
  obtain ⟨n, b, _, he⟩ := ChartLift.Construction.blowupChart_clear_denominator I a x
  have h := congrArg D (congrArg f he)
  rw [map_mul f, map_pow f, D.leibniz, D.leibniz_pow, hD a.val, hD b,
    smul_zero, smul_zero, smul_zero, add_zero] at h
  apply (hc.pow n).left
  simpa only [smul_eq_mul, mul_zero] using h

/-- If the original derivative fixes all hypersurface coefficients, its
blowup lift fixes the entire actual blowup chart of every hypersurface center. -/
theorem blowupChartDerivation_zero_on_subcenter
    (I : Ideal R) (J : Ideal S) (φ : R →+* S) (hIJ : I.map φ ≤ J) (a : I)
    (D : Derivation ℤ S S) (hD : ∀ r : R, D (φ r) = 0) :
    ∀ x : Charts.Construction.blowupChart I a,
      ChartDerivation.Construction.blowupChartDerivation J (SubcenterMap.Construction.subcenterDenominator I J φ hIJ a) D
        (SubcenterMap.Construction.blowupSubcenterMap I J φ hIJ a x) = 0 := by
  apply derivation_zero_on_blowupChart_image I a (SubcenterMap.Construction.blowupSubcenterMap I J φ hIJ a)
    (ChartDerivation.Construction.blowupChartDerivation J (SubcenterMap.Construction.subcenterDenominator I J φ hIJ a) D)
  · rw [SubcenterMap.Construction.blowupSubcenterMap_exceptional]
    exact ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular J (SubcenterMap.Construction.subcenterDenominator I J φ hIJ a)
  · intro r
    rw [SubcenterMap.Construction.blowupSubcenterMap_constants, ChartDerivation.Construction.blowupChartDerivation_constants, hD r, map_zero]
    exact mul_zero (Charts.Construction.blowupChartConstants J (SubcenterMap.Construction.subcenterDenominator I J φ hIJ a)
      (SubcenterMap.Construction.subcenterDenominator I J φ hIJ a).val)

/-- The same lifted derivative still takes the divided normal coordinate to one. -/
theorem blowupChartDerivation_subcenter_normal_coordinate
    (I : Ideal R) (J : Ideal S) (φ : R →+* S) (hIJ : I.map φ ≤ J) (a : I) (z : J)
    (D : Derivation ℤ S S) (hD : ∀ r : R, D (φ r) = 0) (hz : D z.val = 1) :
    ChartDerivation.Construction.blowupChartDerivation J (SubcenterMap.Construction.subcenterDenominator I J φ hIJ a) D
      (ExceptionalIdeal.Construction.blowupChartRatio J (SubcenterMap.Construction.subcenterDenominator I J φ hIJ a) z) = 1 :=
  Coordinate.BlowupTransform.Construction.blowupChartDerivation_coordinate J (SubcenterMap.Construction.subcenterDenominator I J φ hIJ a) z D (hD a.val) hz

variable (I : Ideal R) (J : Ideal S) (φ : R →+* S) (hIJ : I.map φ ≤ J) (a : I)

/-- The transformed ambient chart is an algebra over the actual transformed hypersurface chart. -/
abbrev blowupSubcenterBaseAlgebra :
    Algebra (Charts.Construction.blowupChart I a) (Charts.Construction.blowupChart J (SubcenterMap.Construction.subcenterDenominator I J φ hIJ a)) :=
  (SubcenterMap.Construction.blowupSubcenterMap I J φ hIJ a).toAlgebra

attribute [local instance] blowupSubcenterBaseAlgebra

/-- The lifted normal derivative is relative to the transformed
hypersurface chart, so the same construction can be used at the next step. -/
def blowupSubcenterNormalDerivation (D : Derivation ℤ S S) (hD : ∀ r : R, D (φ r) = 0) :
    Derivation (Charts.Construction.blowupChart I a) (Charts.Construction.blowupChart J (SubcenterMap.Construction.subcenterDenominator I J φ hIJ a))
      (Charts.Construction.blowupChart J (SubcenterMap.Construction.subcenterDenominator I J φ hIJ a)) :=
  Relative.DifferentialBlowup.Construction.ringDerivationOverBase (Charts.Construction.blowupChart I a)
    (ChartDerivation.Construction.blowupChartDerivation J (SubcenterMap.Construction.subcenterDenominator I J φ hIJ a) D)
    (blowupChartDerivation_zero_on_subcenter I J φ hIJ a D hD)

theorem blowupSubcenterNormalDerivation_coordinate (D : Derivation ℤ S S)
    (hD : ∀ r : R, D (φ r) = 0) (z : J) (hz : D z.val = 1) :
    blowupSubcenterNormalDerivation I J φ hIJ a D hD
      (ExceptionalIdeal.Construction.blowupChartRatio J (SubcenterMap.Construction.subcenterDenominator I J φ hIJ a) z) = 1 :=
  blowupChartDerivation_subcenter_normal_coordinate I J φ hIJ a z D hD hz

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.SubcenterDerivation.Construction
