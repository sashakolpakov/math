import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubeClass
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.CubeComposition

/-! # Class Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.Cubical.ClassPullback

noncomputable section

section

/-! The native cubical identity pulls back to every test scheme. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem nativeCubeClass_pullback (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.toOver.left) (ha : Intrinsic.CubeClass.nativeCubeDefect A a = 1)
    {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (x y z : T ⟶ A.toOver) :
    Picard.PicardPullback.picardPullback (x * y * z).left a * Picard.PicardPullback.picardPullback x.left a *
        Picard.PicardPullback.picardPullback y.left a * Picard.PicardPullback.picardPullback z.left a =
      Picard.PicardPullback.picardPullback (x * y).left a * Picard.PicardPullback.picardPullback (x * z).left a *
        Picard.PicardPullback.picardPullback (y * z).left a := by
  have H := congrArg (Picard.PicardPullback.picardPullback (lift (lift x y) z).left)
    ((Intrinsic.CubeClass.nativeCubeDefect_eq_one_iff A a).mp ha)
  change Picard.PicardPullback.picardPullback (lift (lift x y) z).left
      (∏ k : Fin 4, Picard.PicardPullback.picardPullback (Intrinsic.CubeMaps.nativeCubePositiveMap A k).left a) =
    Picard.PicardPullback.picardPullback (lift (lift x y) z).left
      (∏ k : Fin 3, Picard.PicardPullback.picardPullback (Intrinsic.CubeMaps.nativeCubeNegativeMap A k).left a) at H
  rw [map_prod, map_prod] at H
  have hP : (∏ k : Fin 4, Picard.PicardPullback.picardPullback (lift (lift x y) z).left
      (Picard.PicardPullback.picardPullback (Intrinsic.CubeMaps.nativeCubePositiveMap A k).left a)) =
      ∏ k : Fin 4, Picard.PicardPullback.picardPullback (![x * y * z, x, y, z] k).left a := by
    apply Finset.prod_congr rfl
    intro k _
    exact (Picard.PicardPullback.picardPullback_comp _ _ a).trans
      (congrArg (fun f => Picard.PicardPullback.picardPullback f a) (congrArg Over.Hom.left (Intrinsic.CubeComposition.nativeCubePositiveMap_comp A x y z k)))
  have hN : (∏ k : Fin 3, Picard.PicardPullback.picardPullback (lift (lift x y) z).left
      (Picard.PicardPullback.picardPullback (Intrinsic.CubeMaps.nativeCubeNegativeMap A k).left a)) =
      ∏ k : Fin 3, Picard.PicardPullback.picardPullback (![x * y, x * z, y * z] k).left a := by
    apply Finset.prod_congr rfl
    intro k _
    exact (Picard.PicardPullback.picardPullback_comp _ _ a).trans
      (congrArg (fun f => Picard.PicardPullback.picardPullback f a) (congrArg Over.Hom.left (Intrinsic.CubeComposition.nativeCubeNegativeMap_comp A x y z k)))
  have H' := hP.symm.trans (H.trans hN)
  simpa [Fin.prod_univ_succ, mul_assoc] using H'

end

/-! Cubicality gives the two-variable multiplicativity of the difference
class, on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

theorem cubical_group_difference {G : Type*} [CommGroup G]
    (a b c d e f g : G) (h : g * a * b * c = d * e * f) :
    g * a⁻¹ * f⁻¹ = (d * a⁻¹ * b⁻¹) * (e * a⁻¹ * c⁻¹) := by
  calc
    _ = (g * a⁻¹ * f⁻¹) * ((a * a⁻¹) * (b * b⁻¹) * (c * c⁻¹)) := by simp
    _ = (g * a * b * c) * (a⁻¹ * a⁻¹ * b⁻¹ * c⁻¹ * f⁻¹) := by ac_rfl
    _ = (d * e * f) * (a⁻¹ * a⁻¹ * b⁻¹ * c⁻¹ * f⁻¹) := by rw [h]
    _ = (d * a⁻¹ * b⁻¹) * (e * a⁻¹ * c⁻¹) * (f * f⁻¹) := by ac_rfl
    _ = _ := by rw [mul_inv_cancel, mul_one]

def testDifferenceClass (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.toOver.left)
    {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (x y : T ⟶ A.toOver) : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass T.left :=
  Picard.PicardPullback.picardPullback (x * y).left a * (Picard.PicardPullback.picardPullback x.left a)⁻¹ * (Picard.PicardPullback.picardPullback y.left a)⁻¹

theorem testDifferenceClass_mul_right (A : AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass A.toOver.left) (ha : Intrinsic.CubeClass.nativeCubeDefect A a = 1)
    {T : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (x y z : T ⟶ A.toOver) :
    testDifferenceClass A a x (y * z) = testDifferenceClass A a x y * testDifferenceClass A a x z := by
  have H := cubical_group_difference _ _ _ _ _ _ _ (nativeCubeClass_pullback A a ha x y z)
  simpa only [testDifferenceClass, mul_assoc] using H

end

end OAI.RepresentationTheory.Theta.Geometric.Cubical.ClassPullback
