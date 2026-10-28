import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.ChartSmooth
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BasicOpen
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Standard Smooth -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.StandardSmooth

noncomputable section

/-! The actual standard rational projection is smooth of relative
dimension n-m on the complement of its center. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.HomogeneousChartRenaming OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearChart.Hom OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BasicOpen.RationalProjection

theorem away_of_eq {a b : ℕ} (r : ℕ) (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading a →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading b)
    (s : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing a) (t : Foundations.Scheme.ProjectiveSpace.homogeneousCoordinateRing b) (ht : f s = t)
    (hp : Submonoid.powers s ≤ (Submonoid.powers t).comap f)
    (h : RingHom.IsStandardSmoothOfRelativeDimension r (HomogeneousLocalization.map f hp)) :
    RingHom.IsStandardSmoothOfRelativeDimension r (Away.map f s) := by
  subst t
  exact h

variable {m n : ℕ} (j : Fin (m + 1) → Fin (n + 1)) (hj : Function.Injective j)

include hj

theorem away (i : Fin (m + 1)) : RingHom.IsStandardSmoothOfRelativeDimension (n - m)
    (Away.map (HomogeneousChartRenaming.gradedRename j) (MvPolynomial.X i)) := by
  exact away_of_eq (n - m) (HomogeneousChartRenaming.gradedRename j) (MvPolynomial.X i) (MvPolynomial.X (j i))
    (HomogeneousChartRenaming.gradedRename_X j i) (HomogeneousChartRenaming.powers_le j i) (Projection.ChartSmooth.chart j hj i)

theorem affine (i : Fin (m + 1)) : SmoothOfRelativeDimension (n - m)
    (Projective.LinearChart.Hom.affine (HomogeneousChartRenaming.gradedRename j) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X ℂ i) Nat.zero_lt_one) := by
  let f := Away.map (HomogeneousChartRenaming.gradedRename j) (MvPolynomial.X i)
  have hs : SmoothOfRelativeDimension (n - m) (Spec.map (CommRingCat.ofHom f)) := by
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension (n - m))]
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ (away j hj i)
  let := hs
  have hc : SmoothOfRelativeDimension ((n - m) + 0)
      (Spec.map (CommRingCat.ofHom f) ≫ Proj.awayι (Foundations.Scheme.ProjectiveSpace.projectiveGrading m)
        (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i) Nat.zero_lt_one) := inferInstance
  rw [Nat.add_zero] at hc
  exact hc

theorem chart (i : Fin (m + 1)) : SmoothOfRelativeDimension (n - m)
    (Projective.LinearChart.Hom.chart (HomogeneousChartRenaming.gradedRename j) (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X ℂ i) Nat.zero_lt_one) := by
  let := affine j hj i
  have hc : SmoothOfRelativeDimension (0 + (n - m))
      ((Proj.basicOpenIsoSpec (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (HomogeneousChartRenaming.gradedRename j (MvPolynomial.X i))
        ((HomogeneousChartRenaming.gradedRename j).map_mem (MvPolynomial.isHomogeneous_X ℂ i)) Nat.zero_lt_one).hom ≫
        Projective.LinearChart.Hom.affine (HomogeneousChartRenaming.gradedRename j) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X ℂ i) Nat.zero_lt_one) := inferInstance
  rw [Nat.zero_add] at hc
  exact hc

theorem smooth : SmoothOfRelativeDimension (n - m) (Projective.BasicOpen.RationalProjection.map (HomogeneousChartRenaming.gradedRename j)) := by
  let f := HomogeneousChartRenaming.gradedRename j
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension (n - m)) (Projective.BasicOpen.RationalProjection.cover f)
  intro i
  have hs : SmoothOfRelativeDimension (n - m) ((Projective.BasicOpen.RationalProjection.cover f).f i ≫ Projective.BasicOpen.RationalProjection.map f) := by
    change SmoothOfRelativeDimension (n - m)
      ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).homOfLE (le_iSup (Projective.BasicOpen.RationalProjection.coordinateOpen f) i) ≫ Projective.BasicOpen.RationalProjection.map f)
    rw [Projective.BasicOpen.RationalProjection.chart_map]
    exact chart j hj i
  exact hs

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.StandardSmooth
