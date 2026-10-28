import OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.NormalDerivation
import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.BlowupFiber

/-! # Retraction Step -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RetractionStep.Construction

noncomputable section

/-! A retracted étale hypersurface remains retracted after a hypersurface-center blowup. -/

open _root_.Polynomial

universe u

variable {H R : Type u} [CommRing H] [CommRing R]
  [Algebra H R] [Algebra H[X] R] [IsScalarTower H H[X] R]

def etaleLineRetraction (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H) : R →+* H :=
  e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {algebraMap H[X] R X}))

theorem etaleLineRetraction_section
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H) :
    (etaleLineRetraction e).comp Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap = RingHom.id H := by
  apply RingHom.ext
  intro h
  rw [RingHom.comp_apply, NormalDerivation.Construction.etaleLineCoefficientMap_eq]
  exact e.commutes h

omit [Algebra H R] [IsScalarTower H H[X] R] in
theorem etaleLineCenter_eq (K : Ideal H) :
    Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K = K.map (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap (R := R)) ⊔
      Ideal.span {algebraMap H[X] R X} := by
  rw [Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter, PolynomialLineBlowup.Construction.polynomialLineCenter, Ideal.map_sup, Ideal.map_map,
    Ideal.map_span, Set.image_singleton]
  rfl

theorem etaleLineRetraction_center
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H) (K : Ideal H) :
    (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter (R := R) K).map (etaleLineRetraction e) = K := by
  rw [etaleLineCenter_eq, Ideal.map_sup, Ideal.map_map, etaleLineRetraction_section,
    Ideal.map_id, Ideal.map_span, Set.image_singleton]
  have hz : etaleLineRetraction e (algebraMap H[X] R X) = 0 := by
    change e (Ideal.Quotient.mk (Ideal.span {algebraMap H[X] R X}) (algebraMap H[X] R X)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]
  rw [hz, Ideal.span_singleton_zero, sup_bot_eq]

theorem etaleLineRetraction_quotient
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H) (x : R) :
    Ideal.Quotient.mk (Ideal.span {algebraMap H[X] R X})
      (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap (etaleLineRetraction e x)) =
        Ideal.Quotient.mk (Ideal.span {algebraMap H[X] R X}) x := by
  apply e.injective
  rw [NormalDerivation.Construction.etaleLineCoefficientMap_eq]
  exact e.commutes (etaleLineRetraction e x)

variable [Algebra.Etale H[X] R] [IsNoetherianRing R] [Algebra ℚ R]

theorem etaleLineFiber_exceptional_regular (K : Ideal H) (a : K) :
    IsRegular (Ideal.Quotient.mk
      (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a)
        (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K)})
      (Blowup.Charts.Construction.blowupChartConstants (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a)
        (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap a.val))) := by
  apply NoetherianCoordinateTransform.Construction.blowupHypersurface_exceptionalParameter_regular
    (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K)
    ((Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation (H := H) (V := R)).restrictScalars ℤ)
  · exact NormalDerivation.Construction.etaleLineNormalDerivation_coefficient (R := R) a.val
  · exact Retracted.HypersurfaceCenters.Construction.retractedHypersurfaceNormalDerivation_coordinate (H := H) (V := R)

attribute [local instance] Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartBaseAlgebra Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateAlgebra

/-- The new zero fiber is isomorphic over the transformed hypersurface ring
to that very ring; this retains the retraction needed for the next blowup. -/
def etaleLineBlowupFiberEquiv
    (e : (R ⧸ Ideal.span {algebraMap H[X] R X}) ≃ₐ[H] H) (K : Ideal H) (a : K) :
    (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineBlowupChart (R := R) K a ⧸
      Ideal.span {Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateMap (R := R) K a X}) ≃ₐ[Blowup.Charts.Construction.blowupChart K a]
        Blowup.Charts.Construction.blowupChart K a := by
  have hz : etaleLineRetraction e (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement (R := R) K).val = 0 := by
    change e (Ideal.Quotient.mk (Ideal.span {algebraMap H[X] R X}) (algebraMap H[X] R X)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _), map_zero]
  let E := Retracted.BlowupFiber.Construction.retractedBlowupFiberEquiv K (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap
    (etaleLineRetraction e) (etaleLineRetraction_section e) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter_contains_base K)
    (etaleLineRetraction_center e K) a (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K) hz
    (etaleLineRetraction_quotient e) (etaleLineFiber_exceptional_regular K a)
  have he : Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateMap (R := R) K a X =
      ExceptionalIdeal.Construction.blowupChartRatio (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineDenominator (R := R) K a) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K) :=
    Blowups.Etale.RelativeLineBlowup.Construction.etaleLineChartCoordinateMap_coordinate K a
  rw [he]
  refine AlgEquiv.ofRingEquiv (f := E) ?_
  intro x
  change Retracted.BlowupFiber.Construction.retractedBlowupFiberMap K (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap
    (etaleLineRetraction e) (etaleLineRetraction_section e) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter_contains_base K)
    (etaleLineRetraction_center e K) a (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K) hz
      (Retracted.BlowupFiber.Construction.retractedBlowupFiberSection K (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap
        (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter_contains_base K) a (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K) x) = x
  exact RingHom.congr_fun (Retracted.BlowupFiber.Construction.retractedBlowupFiberMap_section K (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter K) Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCoefficientMap
    (etaleLineRetraction e) (etaleLineRetraction_section e) (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineCenter_contains_base K)
    (etaleLineRetraction_center e K) a (Blowups.Etale.RelativeLineBlowup.Construction.etaleLineNormalElement K) hz) x

end

end OAI.AlgebraicGeometry.Resolution.Blowups.EtaleLine.RetractionStep.Construction
