import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RetractionStep
import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.CoefficientTransport

/-! # Ratio Retraction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RatioRetraction.Construction

noncomputable section

/-! Retraction and exact coefficient transform with the actual divided normal equation. -/

open _root_.Polynomial

universe u

variable {H R : Type u} [CommRing H] [CommRing R]
  [Algebra H R] [Algebra H[X] R] [IsScalarTower H H[X] R]
  [Algebra.Etale H[X] R] [IsNoetherianRing R] [Algebra ℚ R]

attribute [local instance] Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartBaseAlgebra

abbrev etaleLineRatioCoordinate (K : Ideal H) (a : K) : Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a :=
  ExceptionalIdeal.Construction.blowupChartRatio (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K)

/-- The retained coefficient ideal after its actual controlled transform
on the quotient by the divided normal equation. -/
def etaleLineTransformedCoefficientIdeal (K : Ideal H) (a : K)
    (C : Ideal (R ⧸ Ideal.span {algebraMap H[X] R X})) (b : ℕ) :
    Ideal (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a ⧸ Ideal.span {etaleLineRatioCoordinate (R := R) K a}) :=
  (C.map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K)
    (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K))).colon
      (Ideal.span {(Ideal.Quotient.mk (Ideal.span {etaleLineRatioCoordinate (R := R) K a})
        (Blowup.Charts.Construction.blowupChartConstants (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a)
          (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap a.val))) ^ b})

/-- The actual zero fiber is the transformed coefficient chart, with its
equation written as the ratio used in the controlled-transform formulas. -/
def etaleLineRatioFiberEquiv
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H) (K : Ideal H) (a : K) :
    (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a ⧸ Ideal.span {etaleLineRatioCoordinate (R := R) K a}) ≃ₐ[Blowup.Charts.Construction.blowupChart K a]
      Blowup.Charts.Construction.blowupChart K a := by
  have hz : RetractionStep.Construction.etaleLineRetraction e (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement (R := R) K).val = 0 := by
    change e (Ideal.Quotient.mk (Ideal.span {algebraMap H[X] R X}) (algebraMap H[X] R X)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]
  let E := Retracted.BlowupFiber.Construction.retractedBlowupFiberEquiv K (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap
    (RetractionStep.Construction.etaleLineRetraction e) (RetractionStep.Construction.etaleLineRetraction_section e) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter_contains_base K)
    (RetractionStep.Construction.etaleLineRetraction_center e K) a (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K) hz
    (RetractionStep.Construction.etaleLineRetraction_quotient e) (RetractionStep.Construction.etaleLineFiber_exceptional_regular K a)
  refine AlgEquiv.ofRingEquiv (f := E) ?_
  intro x
  change Retracted.BlowupFiber.Construction.retractedBlowupFiberMap K (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap
    (RetractionStep.Construction.etaleLineRetraction e) (RetractionStep.Construction.etaleLineRetraction_section e) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter_contains_base K)
    (RetractionStep.Construction.etaleLineRetraction_center e K) a (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K) hz
      (Retracted.BlowupFiber.Construction.retractedBlowupFiberSection K (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap
        (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter_contains_base K) a (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K) x) = x
  exact RingHom.congr_fun (Retracted.BlowupFiber.Construction.retractedBlowupFiberMap_section K (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap
    (RetractionStep.Construction.etaleLineRetraction e) (RetractionStep.Construction.etaleLineRetraction_section e) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter_contains_base K)
    (RetractionStep.Construction.etaleLineRetraction_center e K) a (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K) hz) x

/-- Under the constructed retraction, the retained transformed ideal is
exactly the coefficient ideal's own controlled transform, at the same control. -/
theorem etaleLineRatioFiberEquiv_controlledIdeal
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H) (K : Ideal H) (a : K)
    (C : Ideal (R ⧸ Ideal.span {algebraMap H[X] R X})) (b : ℕ) :
    (etaleLineTransformedCoefficientIdeal K a C b).map (etaleLineRatioFiberEquiv e K a).toRingHom =
      ControlledTransform.Construction.blowupControlledTransform K (C.map e.toRingHom) b a := by
  have hz : RetractionStep.Construction.etaleLineRetraction e (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement (R := R) K).val = 0 := by
    change e (Ideal.Quotient.mk (Ideal.span {algebraMap H[X] R X}) (algebraMap H[X] R X)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]
  exact Retracted.CoefficientTransport.Construction.retractedBlowupFiberEquiv_controlledIdeal K (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap
    (RetractionStep.Construction.etaleLineRetraction e) (RetractionStep.Construction.etaleLineRetraction_section e) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter_contains_base K)
    (RetractionStep.Construction.etaleLineRetraction_center e K) a (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K) hz
    (RetractionStep.Construction.etaleLineRetraction_quotient e) (RetractionStep.Construction.etaleLineFiber_exceptional_regular K a)
    e.toRingHom (fun _ => rfl) C b

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RatioRetraction.Construction
