import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.NormalDerivation

/-! # Reference Base -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.ReferenceBase.Construction

noncomputable section

/-! The repeated normal derivative retains the original coefficient ring. -/

open _root_.Polynomial

universe u

section Subcenter

variable (k : Type u) {H R : Type u} [CommRing k] [CommRing H] [CommRing R]
  [Algebra k H] [Algebra k R]
  (K : Ideal H) (I : Ideal R) (φ : H →+* R) (hKI : K.map φ ≤ I) (a : K)
  (hφ : ∀ c : k, φ (algebraMap k H c) = algebraMap k R c)

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra Blowup.SubcenterDerivation.Construction.blowupSubcenterBaseAlgebra

include hφ in
/-- The transformed hypersurface and ambient chart still have compatible
structure maps from the original coefficient ring. -/
theorem blowupSubcenter_originalScalarTower :
    IsScalarTower k (Blowup.Charts.Construction.blowupChart K a) (Blowup.Charts.Construction.blowupChart I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a)) := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro c
  change Blowup.Charts.Construction.blowupChartConstants I (Blowup.SubcenterMap.Construction.subcenterDenominator K I φ hKI a) (algebraMap k R c) =
    Blowup.SubcenterMap.Construction.blowupSubcenterMap K I φ hKI a (Blowup.Charts.Construction.blowupChartConstants K a (algebraMap k H c))
  rw [Blowup.SubcenterMap.Construction.blowupSubcenterMap_constants, hφ]

end Subcenter

variable (k : Type u) {H R : Type u} [CommRing k] [CommRing H] [CommRing R]
  [Algebra k H] [Algebra k R] [Algebra H R] [IsScalarTower k H R]
  [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartBaseAlgebra
  Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateAlgebra Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_scalarTower Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_algebra_etale

omit [Algebra.Etale H[X] R] in
theorem etaleLineChart_originalScalarTower (K : Ideal H) (a : K) :
    IsScalarTower k (Blowup.Charts.Construction.blowupChart K a) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a) := by
  apply blowupSubcenter_originalScalarTower k K (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap
    (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter_contains_base K) a
  intro c
  rw [NormalDerivation.Construction.etaleLineCoefficientMap_eq]
  exact (IsScalarTower.algebraMap_apply k H R c).symm

attribute [local instance] etaleLineChart_originalScalarTower

/-- Restricting the new normal derivative to the original coefficient ring
gives exactly the derivative used in the repeated coefficient interval theorem. -/
theorem etaleLine_normalDerivation_original_base (K : Ideal H) (a : K) :
    (Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := Blowup.Charts.Construction.blowupChart K a)
      (V := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a)).restrictScalars k =
      Relative.DifferentialBlowup.Construction.blowupRelativeChartDerivation k (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a)
        ((Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := H) (V := R)).restrictScalars k) := by
  rw [NormalDerivation.Construction.etaleLine_normalDerivation_eq_lift]
  apply Derivation.ext
  intro x
  rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.ReferenceBase.Construction
