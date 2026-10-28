import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FramePostcomposeComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SectionChange

/-! # Frame Diagram Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameDiagramPullback.CrystallineFrameDiagramPullback

noncomputable section

/-! A natural geometric map of bounded-frame diagrams induces the
original divided-power de Rham pullback on their frame complexes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u v w
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = fX) (n : ℕ)
  {C : Type v} [Category.{w} C]
  (P : C ⥤ IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fX n)
  (Q : C ⥤ IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n)
  (a : P ⋙ IntegralComparison.BoundedOpen.Equivalence.postcompose g hg n ⟶ Q)

def transformation : Q.op ⋙ FrameComplexFunctor.CrystallineFrameComplexFunctor.bounded fY n ⟶
    P.op ⋙ FrameComplexFunctor.CrystallineFrameComplexFunctor.bounded fX n :=
  Functor.whiskerRight (NatTrans.op a) (FrameComplexFunctor.CrystallineFrameComplexFunctor.bounded fY n) ≫
    Functor.whiskerLeft P.op (FramePostcomposeComplex.CrystallineFramePostcomposeComplex.iso g hg n).hom

theorem component (U : C) : (transformation g hg n P Q a).app (op U) =
    IntegralComparison.RelativeFrame.ChangeNaturality.frameMap (Q.obj U).obj
      ((IntegralComparison.BoundedOpen.Equivalence.postcompose g hg n).obj (P.obj U)).obj (a.app U).hom := by
  change IntegralComparison.RelativeFrame.ChangeNaturality.frameMap (Q.obj U).obj
    ((IntegralComparison.BoundedOpen.Equivalence.postcompose g hg n).obj (P.obj U)).obj (a.app U).hom ≫ 𝟙 _ = _
  exact Category.comp_id _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameDiagramPullback.CrystallineFrameDiagramPullback
