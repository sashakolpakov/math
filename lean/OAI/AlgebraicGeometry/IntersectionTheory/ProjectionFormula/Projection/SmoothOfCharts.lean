import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.StandardSmooth

/-! # Smooth Of Charts -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.SmoothOfCharts

noncomputable section

/-! Smoothness of the actual glued projective projection follows
from standard smoothness of its homogeneous localization chart maps. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.LinearChart.Hom OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BasicOpen.RationalProjection

variable {m n : ℕ} (r : ℕ) (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n)

theorem affine (i : Fin (m + 1))
    (h : RingHom.IsStandardSmoothOfRelativeDimension r (Away.map f (MvPolynomial.X i))) :
    SmoothOfRelativeDimension r (Projective.LinearChart.Hom.affine f (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X ℂ i) Nat.zero_lt_one) := by
  let g := Away.map f (MvPolynomial.X i)
  have hs : SmoothOfRelativeDimension r (Spec.map (CommRingCat.ofHom g)) := by
    rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension r)]
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ h
  let := hs
  have hc : SmoothOfRelativeDimension (r + 0)
      (Spec.map (CommRingCat.ofHom g) ≫ Proj.awayι (Foundations.Scheme.ProjectiveSpace.projectiveGrading m)
        (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X ℂ i) Nat.zero_lt_one) := inferInstance
  rw [Nat.add_zero] at hc
  exact hc

theorem chart (i : Fin (m + 1))
    (h : RingHom.IsStandardSmoothOfRelativeDimension r (Away.map f (MvPolynomial.X i))) :
    SmoothOfRelativeDimension r (Projective.LinearChart.Hom.chart f (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X ℂ i) Nat.zero_lt_one) := by
  let := affine r f i h
  have hc : SmoothOfRelativeDimension (0 + r)
      ((Proj.basicOpenIsoSpec (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f (MvPolynomial.X i))
        (f.map_mem (MvPolynomial.isHomogeneous_X ℂ i)) Nat.zero_lt_one).hom ≫
        Projective.LinearChart.Hom.affine f (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X ℂ i) Nat.zero_lt_one) := inferInstance
  rw [Nat.zero_add] at hc
  exact hc

theorem smooth (h : ∀ i : Fin (m + 1),
    RingHom.IsStandardSmoothOfRelativeDimension r (Away.map f (MvPolynomial.X i))) :
    SmoothOfRelativeDimension r (Projective.BasicOpen.RationalProjection.map f) := by
  apply IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension r) (Projective.BasicOpen.RationalProjection.cover f)
  intro i
  change SmoothOfRelativeDimension r
    ((Foundations.Scheme.ProjectiveSpace.projectiveSpace n).homOfLE (le_iSup (Projective.BasicOpen.RationalProjection.coordinateOpen f) i) ≫ Projective.BasicOpen.RationalProjection.map f)
  rw [Projective.BasicOpen.RationalProjection.chart_map]
  exact chart r f i (h i)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.SmoothOfCharts
