import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RelativeLineBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.HypersurfaceCenters

/-! # Normal Derivation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.NormalDerivation.Construction

noncomputable section

/-! The normal derivative agrees with its blowup lift on the new relative line. -/

open _root_.Polynomial

universe u

variable {H R : Type u} [CommRing H] [CommRing R]
  [Algebra H R] [Algebra H[X] R] [IsScalarTower H H[X] R]
  [Algebra.Etale H[X] R]

omit [Algebra.Etale H[X] R] in
theorem etaleLineCoefficientMap_eq : Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap (H := H) (R := R) = algebraMap H R :=
  (IsScalarTower.algebraMap_eq H H[X] R).symm

theorem etaleLineNormalDerivation_coefficient (h : H) :
    (Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := H) (V := R)).restrictScalars ℤ
      (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap h) = 0 := by
  rw [etaleLineCoefficientMap_eq, Derivation.restrictScalars_apply]
  exact Derivation.map_algebraMap _ h

attribute [local instance] Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartBaseAlgebra Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateAlgebra

theorem etaleLine_normalDerivation_unique (D : Derivation H R R)
    (hD : D (algebraMap H[X] R X) = 1) :
    Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := H) (V := R) = D := by
  apply Blowups.Etale.Derivation.Construction.etaleDerivation_ext (R := H[X])
  have h : (Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := H) (V := R)).compAlgebraMap H[X] =
      D.compAlgebraMap H[X] := by
    apply Polynomial.derivation_ext
    change Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := H) (V := R) (algebraMap H[X] R X) = _
    rw [Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation_coordinate]
    exact hD.symm
  intro p
  exact congrArg (fun E : Derivation H H[X] R => E p) h

/-- The actual blowup lift, viewed over the transformed hypersurface ring. -/
def etaleLineLiftedNormalDerivation (K : Ideal H) (a : K) :
    Derivation (Blowup.Charts.Construction.blowupChart K a) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a)
      (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a) :=
  Blowup.SubcenterDerivation.Construction.blowupSubcenterNormalDerivation K (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap
    (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter_contains_base K) a
    ((Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := H) (V := R)).restrictScalars ℤ)
    etaleLineNormalDerivation_coefficient

theorem etaleLineLiftedNormalDerivation_coordinate (K : Ideal H) (a : K) :
    etaleLineLiftedNormalDerivation (R := R) K a (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateMap K a X) = 1 := by
  rw [Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateMap_coordinate]
  change ChartDerivation.Construction.blowupChartDerivation (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a)
    ((Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := H) (V := R)).restrictScalars ℤ)
    (ExceptionalIdeal.Construction.blowupChartRatio (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a)
      (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K)) = 1
  apply Coordinate.BlowupTransform.Construction.blowupChartDerivation_coordinate
  · exact etaleLineNormalDerivation_coefficient (R := R) a.val
  · exact Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation_coordinate (H := H) (V := R)

attribute [local instance] Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_scalarTower Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_algebra_etale

/-- Étale uniqueness identifies the new normal derivative with the lifted old one.
Thus the derivative used for coefficient transforms is retained at every step. -/
theorem etaleLine_normalDerivation_eq_lift (K : Ideal H) (a : K) :
    Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := Blowup.Charts.Construction.blowupChart K a)
      (V := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a) = etaleLineLiftedNormalDerivation K a := by
  apply etaleLine_normalDerivation_unique
  exact etaleLineLiftedNormalDerivation_coordinate K a

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.NormalDerivation.Construction
