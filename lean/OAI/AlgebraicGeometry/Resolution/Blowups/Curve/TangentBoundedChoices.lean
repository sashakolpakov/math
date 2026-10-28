import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.CurveTangentStep
import OAI.AlgebraicGeometry.Resolution.Blowups.Component.ChoiceBounds
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.Bound
import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.BlowupCover

/-! # Tangent Bounded Choices -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Curve.TangentBoundedChoices.Construction

noncomputable section

/-! Every chart of an actual curve-tangent blowup has a strictly smaller intrinsic coefficient bound. -/

open _root_.Polynomial

universe u

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartBaseAlgebra
  Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateAlgebra Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_scalarTower Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChart_algebra_etale
  EtaleLine.ReferenceBase.Construction.etaleLineChart_originalScalarTower EtaleLine.HorizontalDerivation.Construction.etaleLine_polynomial_originalScalarTower

variable (k : Type u) {H R : Type u} {τ : Type*}
    [Field k] [CharZero k] [IsAlgClosed k] [CommRing H] [CommRing R]
    [Algebra k H] [Algebra k R] [Algebra H R] [IsScalarTower k H R]
    [Algebra H[X] R] [IsScalarTower H H[X] R] [Algebra.Etale H[X] R]
    [Algebra.Smooth k H] [Algebra ℚ R] [IsNoetherianRing R]

theorem etaleLine_curve_tangent_bounded_choices
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H)
    (p : τ → R) (n ℓ : ℕ) (C : Ideal (R ⧸ Ideal.span {algebraMap H[X] R X}))
    (hlow : WeightedGeneratorFamily.Construction.weightedCoordinateDerivativeFamilyIdeal
      (Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := H) (R := R)) (algebraMap H[X] R X) p (n + 1) ≤ C)
    (hupp : C ≤ Relative.CoefficientIdeal.Construction.relativeCoefficientIdeal k (algebraMap H[X] R X) (Ideal.span (Set.range p)) (n + 1))
    (hz : algebraMap H[X] R X ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (Ideal.span (Set.range p)) n)
    (hdim : ringKrullDim H ≤ 1) (hlevel : (n + 1).factorial ≤ ℓ + 1)
    (hbound : Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k C (ℓ + 1) = ⊤) :
    let K := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (C.map e.toRingHom) ℓ
    let I := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K
    ∀ a : Option K,
      ∃ B : Component.CenterChoice.Construction.ComponentCenterChoice k (Blowup.Charts.Construction.blowupChart I (EtaleLine.BlowupCover.Construction.etaleLineChartGenerator K a))
        (ControlledTransform.Construction.blowupControlledTransform I (Ideal.span (Set.range p)) (n + 1) (EtaleLine.BlowupCover.Construction.etaleLineChartGenerator K a)) n,
        B.HasBound ℓ := by
  let K := Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (C.map e.toRingHom) ℓ
  let I := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K
  obtain ⟨hp, _, _, hn, hcoeff⟩ := EtaleLine.CurveTangentStep.Construction.etaleLine_curve_tangent_step k e p n ℓ C hlow hupp hz hdim hlevel hbound
  change ∀ a : Option K, ∃ B : Component.CenterChoice.Construction.ComponentCenterChoice k
    (Blowup.Charts.Construction.blowupChart I (EtaleLine.BlowupCover.Construction.etaleLineChartGenerator K a))
    (ControlledTransform.Construction.blowupControlledTransform I (Ideal.span (Set.range p)) (n + 1) (EtaleLine.BlowupCover.Construction.etaleLineChartGenerator K a)) n, B.HasBound ℓ
  intro a
  cases a with
  | none => exact ⟨.terminal hn, trivial⟩
  | some a =>
      obtain ⟨e', C', _, hu, _, hb, hz'⟩ := hcoeff a
      let z' := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateMap (R := R) K a X
      let D := Retracted.CoefficientStep.Construction.etaleLineOriginalNormalDerivation k (H := Blowup.Charts.Construction.blowupChart K a)
        (R := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a)
      have hd : D z' = 1 := Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation_coordinate
        (H := Blowup.Charts.Construction.blowupChart K a) (V := Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a)
      have hspan := ControlledGeneratorFamily.Construction.blowupControlledTransform_eq_span_family I p (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a) (n + 1) hp
      have hbound := Coefficient.Bound.Construction.retained_coefficient_bound_to_homogenized k z' _ n ℓ C' hu hb
      rw [← hspan] at hbound hz'
      exact ⟨.normal z' D hd hz', hbound⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Curve.TangentBoundedChoices.Construction
