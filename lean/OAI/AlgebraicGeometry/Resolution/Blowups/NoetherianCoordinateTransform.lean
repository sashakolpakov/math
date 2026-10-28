import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.Regularity
import OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfaceCoefficientTransform
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Noetherian Coordinate Transform -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.NoetherianCoordinateTransform.Construction

noncomputable section

/-! Exact hypersurface coefficient transforms over Noetherian rational algebras. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The actual affine charts of a blowup of a Noetherian affine scheme
are Noetherian, without an integrality assumption. -/
theorem blowupChart_isNoetherian (I : Ideal R) (a : I) : IsNoetherianRing (Blowup.Charts.Construction.blowupChart I a) := by
  let : IsLocallyNoetherian (ReesGrading.Construction.affineBlowup I) :=
    LocallyOfFiniteType.isLocallyNoetherian (ReesGrading.Construction.affineBlowupToSpec I)
  have h : IsLocallyNoetherian (Spec (CommRingCat.of (Blowup.Charts.Construction.blowupChart I a))) :=
    isLocallyNoetherian_of_isOpenImmersion
      (Proj.awayι (ReesGrading.Construction.reesGrade I) (Blowup.Charts.Construction.reesGenerator I a) (Blowup.Charts.Construction.reesGenerator_mem I a) (by decide))
  exact isLocallyNoetherian_Spec.mp h

variable [Algebra ℚ R]

local instance (I : Ideal R) (a : I) : Algebra ℚ (Blowup.Charts.Construction.blowupChart I a) :=
  ((Blowup.Charts.Construction.blowupChartConstants I a).comp (algebraMap ℚ R)).toAlgebra

/-- The exceptional parameter is regular on the divided coordinate
hypersurface. No extra regularity hypothesis on that quotient is needed. -/
theorem blowupHypersurface_exceptionalParameter_regular (I : Ideal R) (a z : I)
    (D : Derivation ℤ R R) (ha : D a.val = 0) (hz : D z.val = 1) :
    IsRegular (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
      (Blowup.Charts.Construction.blowupChartConstants I a a.val)) := by
  let : IsNoetherianRing (Blowup.Charts.Construction.blowupChart I a) := blowupChart_isNoetherian I a
  apply Coordinate.Regularity.Construction.regular_mod_coordinate (ChartDerivation.Construction.blowupChartDerivation I a D) _ _
    (ExceptionalIdeal.Construction.blowupChart_exceptionalParameter_regular I a)
  · rw [ChartDerivation.Construction.blowupChartDerivation_constants, ha, map_zero,
      mul_zero (Blowup.Charts.Construction.blowupChartConstants I a a.val)]
  · exact Coordinate.BlowupTransform.Construction.blowupChartDerivation_coordinate I a z D ha hz

/-- Differential coefficient ideals undergo exact controlled transformation
on the hypersurface in every Noetherian coordinate chart. -/
theorem differentialCoefficientIdeal_noetherian_blowup_colon (I J : Ideal R) (a z : I)
    (D : Derivation ℤ R R) (ha : D a.val = 0) (hz : D z.val = 1)
    (b j : ℕ) (hj : j ≤ b) (hJ : J ≤ I ^ b) :
    ((DifferentialCoefficientOrder.Construction.differentialCoefficientIdeal D z.val J j).map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z)).colon
        (Ideal.span {(Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
          (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ^ (b - j)}) =
      HypersurfaceCoefficientTransform.Construction.coordinateDerivativeFamilyIdeal (ChartDerivation.Construction.blowupChartDerivation I a D) (ExceptionalIdeal.Construction.blowupChartRatio I a z)
        (Coordinate.BlowupTransform.Construction.blowupChartTransformSection I J a b hJ) j :=
  HypersurfaceCoefficientTransform.Construction.differentialCoefficientIdeal_blowup_colon I J a z D ha b j hj hJ
    (blowupHypersurface_exceptionalParameter_regular I a z D ha hz)

/-- The entire transformed high-order locus is the simultaneous controlled
coefficient-order locus on its persistent coordinate hypersurface. -/
theorem noetherian_blowup_order_locus_iff_coefficient_transforms
    (I J : Ideal R) (a z : I) (D : Derivation ℤ R R)
    (ha : D a.val = 0) (hz : D z.val = 1) (k : ℕ) (hJ : J ≤ I ^ (k + 1))
    (hzJ : z.val ∈ DifferentialIdealTransform.Construction.iteratedDifferentialIdeal J k) (M : Ideal (Blowup.Charts.Construction.blowupChart I a)) :
    ControlledTransform.Construction.blowupControlledTransform I J (k + 1) a ≤ M ^ (k + 1) ↔
      ExceptionalIdeal.Construction.blowupChartRatio I a z ∈ M ∧ ∀ j < k + 1,
        ((DifferentialCoefficientOrder.Construction.differentialCoefficientIdeal D z.val J j).map (HypersurfaceCoefficientTransform.Construction.blowupHypersurfaceChartMap I a z)).colon
            (Ideal.span {(Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})
              (Blowup.Charts.Construction.blowupChartConstants I a a.val)) ^ (k + 1 - j)}) ≤
          M.map (Ideal.Quotient.mk (Ideal.span {ExceptionalIdeal.Construction.blowupChartRatio I a z})) ^ (k + 1 - j) := by
  rw [HypersurfaceCoefficientTransform.Construction.blowupControlledTransform_order_locus_iff_coordinate_coefficients I J a z D ha hz k hJ hzJ M]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro j
  apply forall_congr'
  intro hj
  rw [differentialCoefficientIdeal_noetherian_blowup_colon I J a z D ha hz (k + 1) j
    (Nat.le_of_lt hj) hJ]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.NoetherianCoordinateTransform.Construction
