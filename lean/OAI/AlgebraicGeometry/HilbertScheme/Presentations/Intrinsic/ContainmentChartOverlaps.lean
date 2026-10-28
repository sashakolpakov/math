import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ContainmentAffineCharts
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Closed.ParameterOverlapIdeals

/-! # Containment Chart Overlaps -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ContainmentChartOverlaps.GradedHilbert

noncomputable section

/-! The actual closed native containment schemes on affine parameter
charts have identical ideal sheaves on every chart overlap. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (B : Over S) [IsLocallyNoetherian B.left] (n : ℕ)
variable (F : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) B)
variable (K : (Hilbert.Functor.ambient (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) B).IdealSheafData)

theorem nativeContainmentChart_overlap (i j : B.left.affineOpenCover.I₀) :
    (ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion B n F K i).left.ker.comap
      (pullback.fst (B.left.affineOpenCover.f i) (B.left.affineOpenCover.f j)) =
    (ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion B n F K j).left.ker.comap
      (pullback.snd (B.left.affineOpenCover.f i) (B.left.affineOpenCover.f j)) := by
  let C := B.left.affineOpenCover
  let W : Over S := Over.mk (pullback.fst (C.f i) (C.f j) ≫ C.f i ≫ B.hom)
  let p : W ⟶ ContainmentAffineCharts.affineParameterChart B i := Over.homMk (pullback.fst (C.f i) (C.f j)) rfl
  let q : W ⟶ ContainmentAffineCharts.affineParameterChart B j := Over.homMk (pullback.snd (C.f i) (C.f j))
    (pullback.condition_assoc B.hom).symm
  have hpq : p ≫ ContainmentAffineCharts.affineParameterChartInclusion B i = q ≫ ContainmentAffineCharts.affineParameterChartInclusion B j :=
    Over.OverMorphism.ext pullback.condition
  exact Closed.ParameterOverlapIdeals.closedParameter_overlap_ideals
    (Ideal.ContainmentParameterFunctor.Hilbert.idealContainmentParameterSubfunctor (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) K F.val)
    (ContainmentAffineCharts.affineParameterChartInclusion B i) (ContainmentAffineCharts.affineParameterChartInclusion B j)
    (ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion B n F K i) (ContainmentAffineCharts.GradedHilbert.nativeContainmentChartInclusion B n F K j)
    (ContainmentAffineCharts.GradedHilbert.nativeContainmentChart_all_tests B n F K i) (ContainmentAffineCharts.GradedHilbert.nativeContainmentChart_all_tests B n F K j) p q hpq

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ContainmentChartOverlaps.GradedHilbert
