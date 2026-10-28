import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.ChartFractions
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BasicOpen
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ProjectionRestriction

/-! # Rational Fractions -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.RationalFractions

noncomputable section

section

/-! The glued rational projection has the expected action on
ratios in every stalk of its domain of definition. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BasicOpen.RationalProjection OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.ChartFractions

variable {m n : ℕ} (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n)
  (i : Fin (m + 1)) (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1)

abbrev variableForm : Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1 := ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℂ i⟩

variable (x : (Projective.BasicOpen.RationalProjection.domain f).toScheme) (hs : f (MvPolynomial.X i) ∉ x.val.asHomogeneousIdeal)

include hs in
theorem target_mem : MvPolynomial.X i ∉ (Projective.BasicOpen.RationalProjection.map f x).asHomogeneousIdeal := by
  have h : x ∈ (Projective.BasicOpen.RationalProjection.domain f).ι ⁻¹ᵁ Proj.basicOpen (Foundations.Scheme.ProjectiveSpace.projectiveGrading n) (f (MvPolynomial.X i)) := hs
  rw [← Projective.BasicOpen.Projection.preimage_basicOpen f (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X ℂ i) (by decide : 0 < 1)] at h
  exact h

theorem pull :
    GermPullback.fraction m (Projective.BasicOpen.RationalProjection.map f) x a (variableForm i) (target_mem f i x hs) =
      GermPullback.fraction n (Projective.BasicOpen.RationalProjection.domain f).ι x (ChartFractions.image f a) (ChartFractions.image f (variableForm i)) hs := by
  let U := Projective.BasicOpen.RationalProjection.coordinateOpen f i
  let y : U.toScheme := ⟨x.val, hs⟩
  let u := (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).homOfLE (le_iSup (Projective.BasicOpen.RationalProjection.coordinateOpen f) i)
  have hy : u y = x := by
    apply Subtype.ext
    exact Scheme.homOfLE_apply (le_iSup (Projective.BasicOpen.RationalProjection.coordinateOpen f) i) y
  have hm : u ≫ Projective.BasicOpen.RationalProjection.map f = Projective.LinearChart.Hom.chart f (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X ℂ i) (by decide : 0 < 1) := Projective.BasicOpen.RationalProjection.chart_map f i
  have hc : MvPolynomial.X i ∉ (Projective.LinearChart.Hom.chart f (MvPolynomial.X i)
      (MvPolynomial.isHomogeneous_X ℂ i) (by decide : 0 < 1) y).asHomogeneousIdeal := by
    rw [← hm]
    simpa only [Scheme.Hom.comp_apply, hy] using target_mem f i x hs
  have hu : u ≫ (Projective.BasicOpen.RationalProjection.domain f).ι = U.ι := Scheme.homOfLE_ι (Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (le_iSup (Projective.BasicOpen.RationalProjection.coordinateOpen f) i)
  have hsy : f (MvPolynomial.X i) ∉ (u y).val.asHomogeneousIdeal := by rw [hy]; exact hs
  apply (ConcreteCategory.bijective_of_isIso
    ((Projective.BasicOpen.RationalProjection.domain f).toScheme.presheaf.stalkCongr (.of_eq hy.symm)).hom).injective
  rw [GermPullback.fraction_point m (Projective.BasicOpen.RationalProjection.map f) x (u y) hy.symm a (variableForm i)
      (target_mem f i x hs) (target_mem f i (u y) hsy),
    GermPullback.fraction_point n (Projective.BasicOpen.RationalProjection.domain f).ι x (u y) hy.symm (ChartFractions.image f a) (ChartFractions.image f (variableForm i)) hs hsy]
  apply (ConcreteCategory.bijective_of_isIso (u.stalkMap y)).injective
  rw [← GermPullback.fraction_comp, ← GermPullback.fraction_comp]
  exact (GermPullback.fraction_congr m _ _ hm y a (variableForm i) _ hc).trans
    ((ChartFractions.chart f (variableForm i) a y hc).trans
      (GermPullback.fraction_congr n _ _ hu.symm y (ChartFractions.image f a) (ChartFractions.image f (variableForm i)) _ _))

end

/-! Coordinate-ratio pullback for a projective projection restricted
to an arbitrary scheme whose image avoids the center. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Restricted

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.ProjectionRestriction OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.ChartFractions OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.RationalFractions

variable {X : Scheme} {m n : ℕ} (f : Foundations.Scheme.ProjectiveSpace.projectiveGrading m →+*ᵍ Foundations.Scheme.ProjectiveSpace.projectiveGrading n)
  (j : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n) (hj : ∀ x : X, j x ∈ Projective.BasicOpen.RationalProjection.domain f)
  (i : Fin (m + 1)) (a : Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1) (x : X)
  (hs : f (MvPolynomial.X i) ∉ (j x).asHomogeneousIdeal)

include hs in
theorem lifted_mem : f (MvPolynomial.X i) ∉ ((Projective.ProjectionRestriction.lift f j hj x).val).asHomogeneousIdeal := by
  have he : (Projective.ProjectionRestriction.lift f j hj x).val = j x := congrArg (fun k : X ⟶ Foundations.Scheme.ProjectiveSpace.projectiveSpace n => k x) (Projective.ProjectionRestriction.lift_fac f j hj)
  rw [he]
  exact hs

include hs in
theorem target_mem : MvPolynomial.X i ∉ (Projective.ProjectionRestriction.projection f j hj x).asHomogeneousIdeal :=
  RationalFractions.target_mem f i (Projective.ProjectionRestriction.lift f j hj x) (lifted_mem f j hj i x hs)

theorem pull :
    GermPullback.fraction m (Projective.ProjectionRestriction.projection f j hj) x a (variableForm i) (target_mem f j hj i x hs) =
      GermPullback.fraction n j x (ChartFractions.image f a) (ChartFractions.image f (variableForm i)) hs := by
  change GermPullback.fraction m (Projective.ProjectionRestriction.lift f j hj ≫ Projective.BasicOpen.RationalProjection.map f)
    x a (variableForm i) _ = _
  rw [GermPullback.fraction_comp]
  calc
    _ = (Projective.ProjectionRestriction.lift f j hj).stalkMap x
      (GermPullback.fraction n (Projective.BasicOpen.RationalProjection.domain f).ι (Projective.ProjectionRestriction.lift f j hj x)
        (ChartFractions.image f a) (ChartFractions.image f (variableForm i)) (lifted_mem f j hj i x hs)) :=
      congrArg ((Projective.ProjectionRestriction.lift f j hj).stalkMap x)
        (RationalFractions.pull f i a (Projective.ProjectionRestriction.lift f j hj x) (lifted_mem f j hj i x hs))
    _ = _ := by
      rw [← GermPullback.fraction_comp]
      exact GermPullback.fraction_congr n _ _ (Projective.ProjectionRestriction.lift_fac f j hj) x (ChartFractions.image f a) (ChartFractions.image f (variableForm i)) _ hs

end Restricted

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.RationalFractions
