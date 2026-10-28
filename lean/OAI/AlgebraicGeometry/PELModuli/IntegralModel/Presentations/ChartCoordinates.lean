import OAI.AlgebraicGeometry.PELModuli.IntegralModel.IntrinsicCoordinateIdeal
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ChartHomogeneousIdeal

/-! # Chart Coordinates -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.ChartCoordinates

noncomputable section

/-! Compare the actual affine projective chart maps used in the native
section calculation and the full corrected Presentations Hilbert predicate. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial

namespace PolarizationEmbedding

universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] {n : ℕ}

theorem e34_dehomogenize_chart_coordinates (i : Fin (n + 1))
    (p : MvPolynomial (Fin (n + 1)) R) :
    SheafCohomology.Projective.SpaceChart.MvPolynomial.chartRingEquiv R i (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i p) = SheafCohomology.Projective.SpaceChart.MvPolynomial.dehomogenizeAux R i p := by
  classical
  have hh (d : ℕ) (p : MvPolynomial (Fin (n + 1)) R) (hp : p.IsHomogeneous d) :
      SheafCohomology.Projective.SpaceChart.MvPolynomial.chartRingEquiv R i (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i p) = SheafCohomology.Projective.SpaceChart.MvPolynomial.dehomogenizeAux R i p := by
    rw [HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize_homogeneous i hp]
    exact SheafCohomology.Projective.SpaceChart.MvPolynomial.dehomogenizeAt_mk R i (by
      simpa only [smul_eq_mul, mul_one] using (mem_homogeneousSubmodule _ _).mpr hp)
  have he : (SheafCohomology.Projective.SpaceChart.MvPolynomial.chartRingEquiv R i).toRingHom.comp (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i) =
      SheafCohomology.Projective.SpaceChart.MvPolynomial.dehomogenizeAux R i := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact hh 0 (C r) (isHomogeneous_C _ r)
    · intro j
      exact hh 1 (X j) (isHomogeneous_X R j)
  exact RingHom.congr_fun he p

theorem singleProjectiveChartAwayIso_awayToSection (i : Fin (n + 1))
    (q : HomogeneousLocalization.Away (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)) :
    let a : Fin 1 → ULift.{u} (Fin (n + 1)) := fun _ => ⟨i⟩
    (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionAwayIso (R := R) a).inv
      ((Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).presheaf.map
        (homOfLE (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a 0)).op
        (Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i) q)) =
      HomogeneousLocalization.awayMap
        (f := X i) (g := SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R) (fun k => (a k).down))
        (x := SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun k => (a k).down)) _
        (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial_mem (R := R) (fun k => (a k).down)) rfl q := by
  classical
  let a : Fin 1 → ULift.{u} (Fin (n + 1)) := fun _ => ⟨i⟩
  let e := SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionAwayIso (R := R) a
  let q' : HomogeneousLocalization.Away (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)
      (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun k => (a k).down)) :=
    HomogeneousLocalization.awayMap
      (f := X i) (g := SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial (R := R) (fun k => (a k).down))
      (x := SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateProductPolynomial (R := R) (fun k => (a k).down)) _
      (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailPolynomial_mem (R := R) (fun k => (a k).down)) rfl q
  have h := ConcreteCategory.congr_hom
    (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionAwayIso_naturality_firstChart (R := R) a) q
  change e.hom q' =
    (Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).presheaf.map
      (homOfLE (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a 0)).op
      (Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i) q) at h
  change e.inv _ = q'
  rw [← h, e.hom_inv_id_apply]

theorem singleProjectiveChartLaurentEquiv_awayToSection (i : Fin (n + 1))
    (q : HomogeneousLocalization.Away (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)) :
    let a : Fin 1 → ULift.{u} (Fin (n + 1)) := fun _ => ⟨i⟩
    SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionLaurentRingEquiv (R := R) a
      ((Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).presheaf.map
        (homOfLE (SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a 0)).op
        (Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i) q)) =
      AddMonoidAlgebra.mapDomain
        (SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun _ : Fin 1 => i))).toAddMonoidHom
        (SheafCohomology.Projective.SpaceChart.MvPolynomial.chartRingEquiv R i q) := by
  classical
  dsimp only [SheafCohomology.Projective.StandardCech.MvPolynomial.coordinateOpenCechIntersectionLaurentRingEquiv, RingEquiv.trans_apply,
    RingEquiv.symm_apply_apply]
  erw [singleProjectiveChartAwayIso_awayToSection i q]
  have h := SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateProductAwayLaurentRingEquiv_awayMap (R := R) (fun _ : Fin 1 => i) q
  have hd : SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.instDecidableEq_oAI = instDecidableEqFin (n + 1) :=
    Subsingleton.elim _ _
  rw [hd] at h
  exact h

theorem singleProjectiveChartRingEquiv_awayToSection (i : Fin (n + 1))
    (q : HomogeneousLocalization.Away (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i)) :
    SingleProjectiveChart.PolarizationEmbedding.singleProjectiveChartRingEquiv i (Proj.awayToSection (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) (X i) q) =
      AddMonoidAlgebra.mapRingEquiv _
        (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm
        (AddMonoidAlgebra.mapDomain
          (SheafCohomology.Projective.LaurentExponentLocalization.MvPolynomial.laurentExponentAwayMap (SheafCohomology.Projective.StandardIntersectionRing.MvPolynomial.coordinateTailExponent (fun _ : Fin 1 => i))).toAddMonoidHom
          (SheafCohomology.Projective.SpaceChart.MvPolynomial.chartRingEquiv R i q)) := by
  rw [SingleProjectiveChart.PolarizationEmbedding.singleProjectiveChartRingEquiv_apply]
  exact congrArg (AddMonoidAlgebra.mapRingEquiv _
    (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm)
      (singleProjectiveChartLaurentEquiv_awayToSection i q)

end PolarizationEmbedding

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Presentations.ChartCoordinates
