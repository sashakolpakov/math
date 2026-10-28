import OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialLineBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.BlowupChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.SubcenterDerivation

/-! # Relative Line Blowup -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RelativeLineBlowup.Construction

noncomputable section

/-! The relative polynomial-line structure persists on actual étale blowup charts. -/

open _root_.Polynomial

universe u

variable {H R : Type u} [CommRing H] [CommRing R] [Algebra H[X] R]

def etaleLineCoefficientMap : H →+* R := (algebraMap H[X] R).comp C

def etaleLineCenter (K : Ideal H) : Ideal R := (PolynomialLineBlowup.Construction.polynomialLineCenter K).map (algebraMap H[X] R)

theorem etaleLineCenter_contains_base (K : Ideal H) :
    K.map (etaleLineCoefficientMap (H := H) (R := R)) ≤ etaleLineCenter K := by
  rw [etaleLineCoefficientMap, ← Ideal.map_map]
  exact Ideal.map_mono le_sup_left

abbrev etaleLineDenominator (K : Ideal H) (a : K) : etaleLineCenter (R := R) K :=
  ⟨algebraMap H[X] R (PolynomialLineBlowup.Construction.polynomialLineDenominator K a).val,
    Ideal.mem_map_of_mem _ (PolynomialLineBlowup.Construction.polynomialLineDenominator K a).property⟩

abbrev etaleLineBlowupChart (K : Ideal H) (a : K) :=
  Blowup.Charts.Construction.blowupChart (etaleLineCenter K) (etaleLineDenominator (R := R) K a)

def etaleLineChartBaseMap (K : Ideal H) (a : K) : Blowup.Charts.Construction.blowupChart K a →+* etaleLineBlowupChart (R := R) K a :=
  Blowup.SubcenterMap.Construction.blowupSubcenterMap K (etaleLineCenter K) etaleLineCoefficientMap (etaleLineCenter_contains_base K) a

/-- The new polynomial line maps into the actual base-changed ambient blowup chart. -/
def etaleLineChartCoordinateMap (K : Ideal H) (a : K) :
    (Blowup.Charts.Construction.blowupChart K a)[X] →+* etaleLineBlowupChart (R := R) K a :=
  (ChartLift.Construction.blowupChartMap (PolynomialLineBlowup.Construction.polynomialLineCenter K) (algebraMap H[X] R) (PolynomialLineBlowup.Construction.polynomialLineDenominator K a)).comp
    (PolynomialLineBlowup.Construction.polynomialLinePolynomialToBlowup K a)

theorem etaleLineChartCoordinateMap_base (K : Ideal H) (a : K) (x : Blowup.Charts.Construction.blowupChart K a) :
    etaleLineChartCoordinateMap (R := R) K a (C x) = etaleLineChartBaseMap K a x := by
  let γ := ChartLift.Construction.blowupChartMap (PolynomialLineBlowup.Construction.polynomialLineCenter K) (algebraMap H[X] R) (PolynomialLineBlowup.Construction.polynomialLineDenominator K a)
  have he : γ.comp (PolynomialLineBlowup.Construction.polynomialLineChartBaseMap K a) = etaleLineChartBaseMap (R := R) K a := by
    apply ChartLift.Construction.blowupChart_hom_ext K a
      ((Blowup.Charts.Construction.blowupChartConstants (etaleLineCenter K) (etaleLineDenominator (R := R) K a)).comp etaleLineCoefficientMap)
      (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular (etaleLineCenter K) (etaleLineDenominator (R := R) K a))
    · intro h
      change γ (PolynomialLineBlowup.Construction.polynomialLineChartBaseMap K a (Blowup.Charts.Construction.blowupChartConstants K a h)) = _
      rw [PolynomialLineBlowup.Construction.polynomialLineChartBaseMap_constants, ChartLift.Construction.blowupChartMap_constants]
      rfl
    · intro h
      exact Blowup.SubcenterMap.Construction.blowupSubcenterMap_constants _ _ _ _ _ h
  change γ (PolynomialLineBlowup.Construction.polynomialLinePolynomialToBlowup K a (C x)) = _
  rw [PolynomialLineBlowup.Construction.polynomialLinePolynomialToBlowup_C]
  exact RingHom.congr_fun he x

def etaleLineNormalElement (K : Ideal H) : etaleLineCenter (R := R) K :=
  ⟨algebraMap H[X] R X, Ideal.mem_map_of_mem _ (PolynomialLineBlowup.Construction.polynomialLineNormalElement K).property⟩

theorem etaleLineChartCoordinateMap_coordinate (K : Ideal H) (a : K) :
    etaleLineChartCoordinateMap (R := R) K a X =
      ExceptionalIdeal.Construction.blowupChartRatio (etaleLineCenter K) (etaleLineDenominator (R := R) K a) (etaleLineNormalElement K) := by
  change ChartLift.Construction.blowupChartMap (PolynomialLineBlowup.Construction.polynomialLineCenter K) (algebraMap H[X] R) (PolynomialLineBlowup.Construction.polynomialLineDenominator K a)
    (PolynomialLineBlowup.Construction.polynomialLinePolynomialToBlowup K a X) = _
  rw [PolynomialLineBlowup.Construction.polynomialLinePolynomialToBlowup_X]
  exact BlowupChart.Construction.blowupChartMap_ratio (PolynomialLineBlowup.Construction.polynomialLineCenter K) (algebraMap H[X] R)
    (PolynomialLineBlowup.Construction.polynomialLineDenominator K a) (PolynomialLineBlowup.Construction.polynomialLineNormalElement K)

variable [Algebra.Etale H[X] R]

/-- The new relative polynomial-coordinate map is étale for every
center ideal in the hypersurface, with no smooth-center assumption needed. -/
theorem etaleLineChartCoordinateMap_etale (K : Ideal H) (a : K) :
    RingHom.Etale (R := (Blowup.Charts.Construction.blowupChart K a)[X]) (S := etaleLineBlowupChart (R := R) K a)
      (etaleLineChartCoordinateMap K a) := by
  apply RingHom.Etale.stableUnderComposition
  · exact RingHom.Etale.of_bijective (PolynomialLineBlowup.Construction.polynomialLineBlowupEquiv K a).symm.bijective
  · exact BlowupChart.Construction.blowupChartMap_ringHom_etale (PolynomialLineBlowup.Construction.polynomialLineCenter K) (PolynomialLineBlowup.Construction.polynomialLineDenominator K a)

abbrev etaleLineChartBaseAlgebra (K : Ideal H) (a : K) :
    Algebra (Blowup.Charts.Construction.blowupChart K a) (etaleLineBlowupChart (R := R) K a) :=
  (etaleLineChartBaseMap K a).toAlgebra

abbrev etaleLineChartCoordinateAlgebra (K : Ideal H) (a : K) :
    Algebra (Blowup.Charts.Construction.blowupChart K a)[X] (etaleLineBlowupChart (R := R) K a) :=
  (etaleLineChartCoordinateMap K a).toAlgebra

attribute [local instance] etaleLineChartBaseAlgebra etaleLineChartCoordinateAlgebra

omit [Algebra.Etale H[X] R] in
theorem etaleLineChart_scalarTower (K : Ideal H) (a : K) :
    IsScalarTower (Blowup.Charts.Construction.blowupChart K a) (Blowup.Charts.Construction.blowupChart K a)[X] (etaleLineBlowupChart (R := R) K a) :=
  IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro x
    exact (etaleLineChartCoordinateMap_base K a x).symm)

theorem etaleLineChart_algebra_etale (K : Ideal H) (a : K) :
    Algebra.Etale (Blowup.Charts.Construction.blowupChart K a)[X] (etaleLineBlowupChart (R := R) K a) :=
  etaleLineChartCoordinateMap_etale K a

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RelativeLineBlowup.Construction
