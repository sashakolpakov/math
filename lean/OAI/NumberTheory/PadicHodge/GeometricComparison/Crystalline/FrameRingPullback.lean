import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameRingFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence

/-! # Frame Ring Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameRingPullback.CrystallineFrameRingPullback

noncomputable section

/-! Geometric postcomposition retains the original ambient frame ring,
so a natural frame map induces its original algebra pullback diagram. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u v w
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = fX) (n : ℕ)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n

def iso : (G).op ⋙ FrameRingFunctor.CrystallineFrameRingFunctor.bounded fY n ≅
    FrameRingFunctor.CrystallineFrameRingFunctor.bounded fX n :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V a
    ext x
    rfl)

variable {C : Type v} [Category.{w} C]
  (P : C ⥤ IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fX n)
  (Q : C ⥤ IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n)
  (a : P ⋙ IntegralComparison.BoundedOpen.Equivalence.postcompose g hg n ⟶ Q)

def transformation : Q.op ⋙ FrameRingFunctor.CrystallineFrameRingFunctor.bounded fY n ⟶
    P.op ⋙ FrameRingFunctor.CrystallineFrameRingFunctor.bounded fX n :=
  Functor.whiskerRight (NatTrans.op a) (FrameRingFunctor.CrystallineFrameRingFunctor.bounded fY n) ≫
    Functor.whiskerLeft P.op (iso g hg n).hom

theorem component (U : C) : (transformation g hg n P Q a).app (op U) =
    (FrameRingFunctor.CrystallineFrameRingFunctor.bounded fY n).map (a.app U).op :=
  Category.comp_id _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameRingPullback.CrystallineFrameRingPullback
