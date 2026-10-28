import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartOverlapCover
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.Overlap
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.MonomialFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BoundaryTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.MonomialResidualTransform

/-! # Blowup Overlap -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BlowupOverlap.Construction

noncomputable section

/-! Étale boundary coordinates on a common refinement of any center chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {σ k S : Type u} [DecidableEq σ] [Field k] [CommRing S]
  [Algebra (MvPolynomial σ k) S]

abbrev coordinateBlowupOverlap (C : Finset σ)
    (a : Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) (i : C) :=
  Blowup.ChartOverlap.Construction.blowupChartOverlap (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) a
    (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)

def coordinateBlowupOverlapMap (C : Finset σ)
    (a : Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) (i : C) :
    MvPolynomial σ k →+* coordinateBlowupOverlap C a i :=
  (Blowup.ChartOverlap.Construction.blowupChartOverlapRight _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)).comp
    (Blowups.Etale.MonomialStep.Construction.etaleSubsetCoordinateMap (R := k) (S := S) C i)

variable [Algebra.Etale (MvPolynomial σ k) S]

theorem coordinateBlowupOverlapMap_etale (C : Finset σ)
    (a : Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) (i : C) :
    (coordinateBlowupOverlapMap C a i).Etale :=
  RingHom.Etale.stableUnderComposition _ _ (Blowups.Etale.MonomialStep.Construction.etaleSubsetCoordinateMap_etale C i)
    (Blowup.Overlap.Construction.blowupChartOverlapRight_etale _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i))

variable [Algebra k S] [IsScalarTower k (MvPolynomial σ k) S]

omit [Algebra.Etale (MvPolynomial σ k) S] in
theorem coordinateBlowupOverlapMap_ground (C : Finset σ)
    (a : Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) (i : C) (c : k) :
    coordinateBlowupOverlapMap C a i (MvPolynomial.C c) =
      Blowup.ChartOverlap.Construction.blowupChartOverlapConstants _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i) (algebraMap k S c) := by
  rw [coordinateBlowupOverlapMap, RingHom.comp_apply, Blowups.Etale.Monomial.Construction.etaleSubsetCoordinateMap_C,
    Blowup.ChartOverlap.Construction.blowupChartOverlapRight_constants]
  congr 1
  exact (IsScalarTower.algebraMap_apply k (MvPolynomial σ k) S c).symm

omit [Algebra.Etale (MvPolynomial σ k) S] [Algebra k S]
  [IsScalarTower k (MvPolynomial σ k) S] in
/-- The original chart's exceptional equation is a unit times the new
denominator coordinate on this actual common open chart. -/
theorem coordinateBlowupOverlap_exceptional (C : Finset σ)
    (a : Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) (i : C) :
    Blowup.ChartOverlap.Construction.blowupChartOverlapLeft _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i) (Blowup.Charts.Construction.blowupChartConstants _ a a.val) =
      Blowup.ChartOverlap.Construction.blowupChartOverlapRight _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)
          (ExceptionalIdeal.Construction.blowupChartRatio _ (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i) a) *
        coordinateBlowupOverlapMap C a i (MvPolynomial.X i.val) := by
  rw [Blowup.ChartOverlap.Construction.blowupChartOverlapLeft_constants, coordinateBlowupOverlapMap, RingHom.comp_apply,
    MonomialResidualTransform.Construction.etaleSubsetCoordinateMap_self, Blowup.ChartOverlap.Construction.blowupChartOverlapRight_constants,
    mul_comm (Blowup.ChartOverlap.Construction.blowupChartOverlapRight _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)
      (ExceptionalIdeal.Construction.blowupChartRatio _ (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i) a))]
  exact (Blowup.OverlapTransitions.Construction.blowupChartOverlapRight_factorization _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i) a).symm

omit [Algebra.Etale (MvPolynomial σ k) S] [Algebra k S]
  [IsScalarTower k (MvPolynomial σ k) S] in
/-- All old center-boundary equations retain their coordinate labels;
the chosen denominator label has unit divided transform. -/
theorem coordinateBlowupOverlap_boundary (C : Finset σ)
    (a : Blowups.Etale.CoefficientStep.Construction.etaleCoordinateIdeal (K := k) (S := S) C) (i j : C) :
    Blowup.ChartOverlap.Construction.blowupChartOverlapLeft _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)
        (ExceptionalIdeal.Construction.blowupChartRatio _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C j)) =
      Blowup.ChartOverlap.Construction.blowupChartOverlapLeft _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)
          (ExceptionalIdeal.Construction.blowupChartRatio _ a (Blowups.Etale.CoefficientStep.Construction.etaleCoordinateElement C i)) *
        (if j.val = i.val then 1 else coordinateBlowupOverlapMap C a i (MvPolynomial.X j.val)) := by
  rw [Blowup.OverlapTransitions.Construction.blowupChartOverlap_ratio_transition]
  by_cases hji : j.val = i.val
  · have he : j = i := Subtype.ext hji
    subst j
    rw [ite_eq_left rfl, Blowups.Etale.CoefficientStep.Construction.blowupChartRatio_self, map_one]
  · rw [ite_eq_right hji, coordinateBlowupOverlapMap, RingHom.comp_apply,
      TransformedHypersurfaceCoordinates.Construction.etaleSubsetCoordinateMap_center C i j hji]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.BlowupOverlap.Construction
