import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.IntegerQuotient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.SectionMap
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Localization

/-! # Saturated Cech Augmentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SaturatedCechAugmentation.GradedHilbert

noncomputable section

/-! The actual Čech augmentation of a saturated homogeneous coordinate ideal is injective in every nonnegative degree. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.SectionMap.ProjectiveCech

universe u

variable {R : Type u} [CommRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)

include hSat in
theorem saturatedDegreeSectionMap_eq_zero (d : ℕ) (x : Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I (d : ℤ))
    (hx : Cech.SectionMap.ProjectiveCech.moduleDegreeSectionMap (σ := Fin (n + 1)) R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) x = 0) : x = 0 := by
  have hm : x.val ∈ Graded.Quotient.GradedHilbert.quotientGrading I d := (le_of_eq (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading_nat I d)) x.property
  obtain ⟨p, hp, hpx⟩ := hm
  apply Subtype.ext
  change x.val = 0
  change Ideal.Quotient.mk I.toIdeal p = x.val at hpx
  rw [← hpx]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply hSat.mem_of_variable_powers p d hp
  intro i
  have hz := congrFun hx {i}
  rw [Cech.SectionMap.ProjectiveCech.moduleDegreeSectionMap_singleton, ← hpx] at hz
  obtain ⟨k, hk⟩ := (Module.Fractions.GradedModules.moduleFractionMap_eq_zero (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R {i}) 0 _).mp hz
  rw [EventualDegreeFlatness.ProjectiveCech.inversionMonomial_singleton] at hk
  exact ⟨k, Ideal.Quotient.eq_zero_iff_mem.mp hk⟩

include hSat in
theorem saturatedDegreeSectionMap_injective (d : ℕ) :
    Function.Injective (Cech.SectionMap.ProjectiveCech.moduleDegreeSectionMap (σ := Fin (n + 1)) R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply saturatedDegreeSectionMap_eq_zero I hSat d (x - y)
  rw [map_sub, hxy, sub_self]

include hSat in
theorem saturatedCechAugmentation_injective (d : ℕ) :
    Function.Injective (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) 0) := by
  let E := Cech.AugmentationDegree.ProjectiveCech.moduleCechAugmentationEquiv (σ := Fin (n + 1)) R
    (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)
  have hcomp (f : ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := Fin (n + 1)) R
      (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) 0) :
      Cech.SectionMap.ProjectiveCech.moduleDegreeSectionMap R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) (E f) =
        (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) 0 f).val := by
    rw [Cech.SectionMap.ProjectiveCech.moduleDegreeSectionMap, Cech.AugmentationMap.ProjectiveCech.moduleAugmentationToTerm_equiv]
    change (ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) 0 (E.symm (E f))).val = _
    rw [E.symm_apply_apply]
  intro f g hfg
  apply E.injective
  apply saturatedDegreeSectionMap_injective I hSat d
  rw [hcomp, hcomp, hfg]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SaturatedCechAugmentation.GradedHilbert
