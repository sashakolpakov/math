import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.ReferenceBase
import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RetractionStep
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.IntervalCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.CoefficientTransport

/-! # Coefficient Step -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.CoefficientStep.Construction

noncomputable section

/-! Coefficient induction on successive retracted étale line charts. -/

open _root_.Polynomial

universe u

variable (k : Type u) {H R : Type u} [CommRing k] [CommRing H] [CommRing R]
  [Algebra k H] [Algebra k R] [Algebra H R] [IsScalarTower k H R]
  [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]

abbrev etaleLineOriginalNormalDerivation : Derivation k R R :=
  (HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := H) (V := R)).restrictScalars k

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartBaseAlgebra
  Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateAlgebra Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_scalarTower Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_algebra_etale
  EtaleLine.ReferenceBase.Construction.etaleLineChart_originalScalarTower

/-- The coefficient interval is retained with the newly constructed normal
derivative on the next actual étale chart. The original coefficient ring and
generator index set remain fixed, so this is the same hypothesis for the next step. -/
theorem etaleLine_coefficient_interval_transform [IsNoetherianRing R] [Algebra ℚ R]
    {ι : Type*} (K : Ideal H) (a : K) (p : ι → R) (b : ℕ)
    (hp : Ideal.span (Set.range p) ≤ Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K ^ b)
    (C : Ideal (R ⧸ Ideal.span {algebraMap H[X] R X}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal
      (etaleLineOriginalNormalDerivation k (H := H) (R := R)) (algebraMap H[X] R X) p b ≤ C)
    (hupp : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (algebraMap H[X] R X) (Ideal.span (Set.range p)) b) :
    let z' := ExceptionalIdeal.Construction.blowupChartRatio (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a)
      (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K)
    let p' := ControlledGeneratorFamily.Construction.blowupChartTransformFamily (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) p (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a) b hp
    let C' := (C.map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K)
      (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K))).colon
        (Ideal.span {(Ideal.Quotient.mk (Ideal.span {z'})
          (Blowup.Charts.Construction.blowupChartConstants (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a)
            (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a).val)) ^ b.factorial})
    WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal
        (etaleLineOriginalNormalDerivation k (H := Blowup.Charts.Construction.blowupChart K a)
          (R := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a)) z' p' b ≤ C' ∧
      C' ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z' (Ideal.span (Set.range p')) b := by
  have ha : etaleLineOriginalNormalDerivation k (H := H) (R := R)
      (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a).val = 0 :=
    EtaleLine.NormalDerivation.Construction.etaleLineNormalDerivation_coefficient (H := H) (R := R) a.val
  have hz : etaleLineOriginalNormalDerivation k (H := H) (R := R)
      (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement (R := R) K).val = 1 :=
    HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation_coordinate (H := H) (V := R)
  have hstep := Relative.CoefficientFamilyInterval.Construction.relative_coefficient_family_interval_transform k (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K)
    (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K)
    (etaleLineOriginalNormalDerivation k (H := H) (R := R)) ha hz p b hp C hlow hupp
  have hD : etaleLineOriginalNormalDerivation k (H := Blowup.Charts.Construction.blowupChart K a)
      (R := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a) =
      Relative.DifferentialBlowup.Construction.blowupRelativeChartDerivation k (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a)
        (etaleLineOriginalNormalDerivation k (H := H) (R := R)) :=
    EtaleLine.ReferenceBase.Construction.etaleLine_normalDerivation_original_base k K a
  refine ⟨?_, hstep.2⟩
  have he := congrArg (fun D : Derivation k (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a)
      (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a) => WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal D
        (ExceptionalIdeal.Construction.blowupChartRatio (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K))
        (ControlledGeneratorFamily.Construction.blowupChartTransformFamily (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) p (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a) b hp) b) hD
  exact he.le.trans hstep.1

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.CoefficientStep.Construction
