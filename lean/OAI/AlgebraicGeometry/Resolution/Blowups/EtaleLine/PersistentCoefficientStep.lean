import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.FrameCoefficientStep
import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.FamilyCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.UnitBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.MaximumOrderTransform

/-! # Persistent Coefficient Step -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.PersistentCoefficientStep.Construction

noncomputable section

/-! Persistent maximal-contact data and the terminal chart in an actual coefficient step. -/

open _root_.Polynomial _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) {H R : Type u} {τ : Type*}
  [CommRing k] [CommRing H] [CommRing R]
  [Algebra k H] [Algebra k R] [Algebra H R] [IsScalarTower k H R]
  [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]
  [IsNoetherianRing R] [Algebra ℚ R]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartBaseAlgebra
  Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateAlgebra Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_scalarTower Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_algebra_etale
  ReferenceBase.Construction.etaleLineChart_originalScalarTower HorizontalDerivation.Construction.etaleLine_polynomial_originalScalarTower

/-- Every coefficient chart reconstructs the hypotheses in the actual next
polynomial coordinate, including the exact coefficient transform and the
persistent maximal-contact equation. -/
theorem etaleLine_persistent_coefficient_chart
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H)
    (K : Ideal H) (a : K) (p : τ → R) (n : ℕ)
    (hp : Ideal.span (Set.range p) ≤ Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K ^ (n + 1))
    (hz : algebraMap H[X] R X ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Ideal.span (Set.range p)) n)
    (C : Ideal (R ⧸ Ideal.span {algebraMap H[X] R X}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal
      (Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R))
      (algebraMap H[X] R X) p (n + 1) ≤ C)
    (hupp : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (algebraMap H[X] R X)
      (Ideal.span (Set.range p)) (n + 1)) :
    let z' := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateMap (R := R) K a X
    let p' := ControlledGeneratorFamily.Construction.blowupChartTransformFamily (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) p
      (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a) (n + 1) hp
    ∃ (e' : (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a ⧸ Ideal.span {z'}) ≃ₐ[Blowup.Charts.Construction.blowupChart K a]
        Blowup.Charts.Construction.blowupChart K a)
      (C' : Ideal (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a ⧸ Ideal.span {z'})),
      WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal
        (Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := Blowup.Charts.Construction.blowupChart K a)
          (R := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a)) z' p' (n + 1) ≤ C' ∧
      C' ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k z' (Ideal.span (Set.range p')) (n + 1) ∧
      C'.map e'.toRingHom = ControlledTransform.Construction.blowupControlledTransform K (C.map e.toRingHom) (n + 1).factorial a ∧
      z' ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Ideal.span (Set.range p')) n := by
  dsimp only
  rw [Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateMap_coordinate]
  refine ⟨RatioRetraction.Construction.etaleLineRatioFiberEquiv e K a,
    RatioRetraction.Construction.etaleLineTransformedCoefficientIdeal K a C (n + 1).factorial, ?_⟩
  obtain ⟨hlow', hupp'⟩ := Retracted.CoefficientStep.Construction.etaleLine_coefficient_interval_transform k K a p (n + 1) hp C hlow hupp
  refine ⟨hlow', hupp', RatioRetraction.Construction.etaleLineRatioFiberEquiv_controlledIdeal e K a C (n + 1).factorial, ?_⟩
  rw [← ControlledGeneratorFamily.Construction.blowupControlledTransform_eq_span_family]
  exact Relative.HypersurfacePersistence.Construction.blowupChart_relative_hypersurface_persists k (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K)
    (Ideal.span (Set.range p)) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a)
    (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K) n hp hz

omit [Algebra k H] [Algebra H R] [IsScalarTower k H R]
  [IsScalarTower H H[X] R] [Algebra.Etale H[X] R] [IsNoetherianRing R] [Algebra ℚ R] in
/-- The normal-denominator member of the same actual blowup cover is
terminal at the unchanged ambient control. -/
theorem etaleLine_normal_chart_terminal
    (K : Ideal H) (J : Ideal R) (n : ℕ) (hJ : J ≤ Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K ^ (n + 1))
    (hz : algebraMap H[X] R X ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
      (ControlledTransform.Construction.blowupControlledTransform (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) J (n + 1)
        (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement (R := R) K)) n = ⊤ :=
  Coefficient.UnitBlowup.Construction.relative_hypersurface_denominator_differential_unit k (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) J
    (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement (R := R) K) n hJ hz

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.PersistentCoefficientStep.Construction
