import OAI.AlgebraicGeometry.Resolution.Blowups.ExceptionalIdeal
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Chart Overlap -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartOverlap.Construction

noncomputable section

/-! Actual common principal-open rings of two Rees blowup charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] (I : Ideal R) (a b : I)

/-- The homogeneous localization defining the intersection of two charts. -/
abbrev blowupChartOverlap :=
  HomogeneousLocalization.Away (ReesGrading.Construction.reesGrade I) (Charts.Construction.reesGenerator I a * Charts.Construction.reesGenerator I b)

def blowupChartOverlapLeft : Charts.Construction.blowupChart I a →+* blowupChartOverlap I a b :=
  HomogeneousLocalization.awayMap (ReesGrading.Construction.reesGrade I) (Charts.Construction.reesGenerator_mem I b) rfl

def blowupChartOverlapRight : Charts.Construction.blowupChart I b →+* blowupChartOverlap I a b :=
  HomogeneousLocalization.awayMap (ReesGrading.Construction.reesGrade I) (Charts.Construction.reesGenerator_mem I a)
    (mul_comm (Charts.Construction.reesGenerator I a) (Charts.Construction.reesGenerator I b))

def blowupChartOverlapConstants : R →+* blowupChartOverlap I a b :=
  (HomogeneousLocalization.fromZeroRingHom (ReesGrading.Construction.reesGrade I)
    (Submonoid.powers (Charts.Construction.reesGenerator I a * Charts.Construction.reesGenerator I b))).comp
      (algebraMap R (ReesGrading.Construction.reesGrade I 0))

theorem blowupChartOverlapLeft_constants (r : R) :
    blowupChartOverlapLeft I a b (Charts.Construction.blowupChartConstants I a r) =
      blowupChartOverlapConstants I a b r :=
  HomogeneousLocalization.awayMap_fromZeroRingHom _ _ _ _

theorem blowupChartOverlapRight_constants (r : R) :
    blowupChartOverlapRight I a b (Charts.Construction.blowupChartConstants I b r) =
      blowupChartOverlapConstants I a b r :=
  HomogeneousLocalization.awayMap_fromZeroRingHom _ _ _ _

/-- This actual intersection ring is obtained by inverting `b/a` in chart `a`. -/
theorem blowupChartOverlapLeft_isLocalization :
    letI := (blowupChartOverlapLeft I a b).toAlgebra
    IsLocalization.Away (ExceptionalIdeal.Construction.blowupChartRatio I a b) (blowupChartOverlap I a b) := by
  have he : HomogeneousLocalization.Away.isLocalizationElem
      (Charts.Construction.reesGenerator_mem I a) (Charts.Construction.reesGenerator_mem I b) = ExceptionalIdeal.Construction.blowupChartRatio I a b := by
    simp only [HomogeneousLocalization.Away.isLocalizationElem, ExceptionalIdeal.Construction.blowupChartRatio, pow_one]
  rw [← he]
  exact HomogeneousLocalization.Away.isLocalization_mul
    (Charts.Construction.reesGenerator_mem I a) (Charts.Construction.reesGenerator_mem I b) rfl (by decide : 1 ≠ 0)

/-- The same ring is obtained by inverting `a/b` in chart `b`. -/
theorem blowupChartOverlapRight_isLocalization :
    letI := (blowupChartOverlapRight I a b).toAlgebra
    IsLocalization.Away (ExceptionalIdeal.Construction.blowupChartRatio I b a) (blowupChartOverlap I a b) := by
  have he : HomogeneousLocalization.Away.isLocalizationElem
      (Charts.Construction.reesGenerator_mem I b) (Charts.Construction.reesGenerator_mem I a) = ExceptionalIdeal.Construction.blowupChartRatio I b a := by
    simp only [HomogeneousLocalization.Away.isLocalizationElem, ExceptionalIdeal.Construction.blowupChartRatio, pow_one]
  rw [← he]
  exact HomogeneousLocalization.Away.isLocalization_mul
    (Charts.Construction.reesGenerator_mem I b) (Charts.Construction.reesGenerator_mem I a)
    (mul_comm (Charts.Construction.reesGenerator I a) (Charts.Construction.reesGenerator I b)) (by decide : 1 ≠ 0)

theorem blowupChartOverlapLeft_isOpenImmersion :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (blowupChartOverlapLeft I a b))) := by
  let := (blowupChartOverlapLeft I a b).toAlgebra
  let := blowupChartOverlapLeft_isLocalization I a b
  exact IsOpenImmersion.of_isLocalization (ExceptionalIdeal.Construction.blowupChartRatio I a b)

theorem blowupChartOverlapRight_isOpenImmersion :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (blowupChartOverlapRight I a b))) := by
  let := (blowupChartOverlapRight I a b).toAlgebra
  let := blowupChartOverlapRight_isLocalization I a b
  exact IsOpenImmersion.of_isLocalization (ExceptionalIdeal.Construction.blowupChartRatio I b a)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartOverlap.Construction
