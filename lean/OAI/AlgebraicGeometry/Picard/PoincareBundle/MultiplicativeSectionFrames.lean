import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.SectionFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineData
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison

/-! # Multiplicative Section Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeSectionFrames

noncomputable section

/-! A normalized multiplicative section of an actual line bundle on a group scheme is everywhere a frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeLineData OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Comparison.Bundle

variable {S : Scheme.{u}} {H : Over S} [GrpObj H]
  (L : Line.Bundles.LineBundle H.left) (D : MultiplicativeLineData.MultiplicativeData L)
  (s : ∀ (T : Over S) (a : T ⟶ H), AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ⟶ Line.Fibers.fiber L a)
  (hu : ∀ T : Over S, s T 1 = D.unitFrame.hom)
  (hm : ∀ (T : Over S) (a b c : T ⟶ H) (h : a * b = c) (U : T.left.Opens),
    (D.product a b c h).app U ((s T a).app U (1 : Γ(T.left, U)))
      ((s T b).app U (1 : Γ(T.left, U))) = (s T c).app U (1 : Γ(T.left, U)))

include hu hm

/-- Multiplication with the inverse point proves that the section is an actual frame on every test scheme. -/
theorem isIso (T : Over S) (a : T ⟶ H) : IsIso (s T a) := by
  have hβ : IsIso (Bilinear.BilinearPullback.toHom (D.product a a⁻¹ 1 (mul_inv_cancel a))) :=
    D.product_isIso a a⁻¹ 1 (mul_inv_cancel a)
  have h : ∀ U : T.left.Opens,
      (D.product a a⁻¹ 1 (mul_inv_cancel a)).app U ((s T a).app U (1 : Γ(T.left, U)))
        ((s T a⁻¹).app U (1 : Γ(T.left, U))) = D.unitFrame.hom.app U (1 : Γ(T.left, U)) := by
    intro U
    exact (hm T a a⁻¹ 1 (mul_inv_cancel a) U).trans
      (congrArg (fun f => f.app U (1 : Γ(T.left, U))) (hu T))
  exact (@Bilinear.SectionFrames.isIso_of_product T.left (Line.Comparison.Bundle.toShared (L.pullback a.left))
    (Line.Comparison.Bundle.toShared (L.pullback a⁻¹.left)) (Line.Fibers.fiber L (1 : T ⟶ H))
    (D.product a a⁻¹ 1 (mul_inv_cancel a)) hβ
    (s T a) (s T a⁻¹) D.unitFrame.hom D.unitFrame.isIso_hom h).1

/-- The normalized multiplicative section supplies a genuine trivialization, without reducedness assumptions. -/
def frame (T : Over S) (a : T ⟶ H) : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L a :=
  @asIso _ _ _ _ (s T a) (isIso L D s hu hm T a)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.MultiplicativeSectionFrames
