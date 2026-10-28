import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackSheafNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor

/-! # Diagram Pullback -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.DiagramPullback.BoundedFrameDiagramPullback

noncomputable section

/-! A natural geometric map of bounded-frame diagrams induces a
natural pullback of their original augmented sheaf resolutions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u v w
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated fX] [IsSeparated fY]
  (g : X ⟶ Y) (hg : g ≫ fY = fX) (n : ℕ)
  {C : Type v} [Category.{w} C]
  (P : C ⥤ IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fX n)
  (Q : C ⥤ IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n)
  (a : P ⋙ IntegralComparison.BoundedOpen.Equivalence.postcompose g hg n ⟶ Q)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p) (J := J) (δ := δ) g hg n

def transformation : Q.op ⋙ ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor fY n ⋙
    (R).mapHomologicalComplex (.up ℕ) ⟶
      P.op ⋙ ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor fX n where
  app U := PullbackSheaf.BoundedFramePullbackSheaf.map g hg n (P.obj U.unop) (Q.obj U.unop) (a.app U.unop)
  naturality U V h := PullbackSheafNaturality.BoundedFramePullbackSheafNaturality.natural g hg n
    (P.map h.unop) (Q.map h.unop) (a.app V.unop) (a.app U.unop) (a.naturality h.unop)

theorem augmentation (U : C) :
    IntegralComparison.BoundedFrame.PullbackAugmentation.augmentation g hg n (Q.obj U) ≫
      (transformation g hg n P Q a).app (op U) =
    IntegralComparison.Bounded.RelativeSheafComplex.augmentation fX n (P.obj U) :=
  PullbackSheaf.BoundedFramePullbackSheaf.augmentation g hg n (P.obj U) (Q.obj U) (a.app U)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.DiagramPullback.BoundedFrameDiagramPullback
