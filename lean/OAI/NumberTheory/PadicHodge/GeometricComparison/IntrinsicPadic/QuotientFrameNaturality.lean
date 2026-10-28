import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientFrameIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.LocalQuotientMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicRingHomExt

/-! # Quotient Frame Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientFrameNaturality.IntrinsicPadicQuotientFrameNaturality

noncomputable section

/-! Naturality of the componentwise identification of native quotient algebras
with the original crystalline frame algebras. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientFrameIso.IntrinsicPadicQuotientFrameIso

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "quotients" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AlgebraQuotient.IntrinsicPadicAlgebraQuotient.functor p X n
local notation "ambient" => OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameRingFunctor.CrystallineFrameRingFunctor.bounded
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n

theorem composed_raw_local {I J : X.left.affineOpens} (α : I ⟶ J) :
    (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp I).inv.hom.toRingHom.comp
      ((PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp
        I.val J.val I.property J.property (leOfHom α) n).hom.ringMap.toRingHom.comp
          (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp J).hom.hom.toRingHom) =
    (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp I).inv.hom.toRingHom.comp
      ((PadicFrameRestriction.IntrinsicPadicFrameRestriction.localMap p X Y f hp
        I.val J.val I.property J.property (leOfHom α) n).hom.ringMap.toRingHom.comp
          (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp J).hom.hom.toRingHom) :=
  congrArg (fun ρ :
      (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp J.val J.property n).obj.ring →+*
        (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp I.val I.property n).obj.ring => (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp I).inv.hom.toRingHom.comp
    (ρ.comp (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp J).hom.hom.toRingHom))
      (LocalQuotientMap.IntrinsicPadicLocalQuotientMap.raw_to_local p X Y f hp n α)

theorem ringHom_eq {I J : X.left.affineOpens} (α : I ⟶ J) :
    (QuotientFrameIso.IntrinsicPadicQuotientFrameIso.conjugatedMap p X Y f hp n α).hom.toRingHom = ((quotients).map α.op).hom.toRingHom :=
  (QuotientFrameIso.IntrinsicPadicQuotientFrameIso.conjugatedMap_ringHom p X Y f hp n α).trans
    ((composed_raw_local p X Y f hp n α).trans (LocalQuotientMap.IntrinsicPadicLocalQuotientMap.local_formula p X Y f hp n α))

theorem conjugatedMap_eq {I J : X.left.affineOpens} (α : I ⟶ J) :
    QuotientFrameIso.IntrinsicPadicQuotientFrameIso.conjugatedMap p X Y f hp n α = (quotients).map α.op :=
  AlgebraicRingHomExt.CommAlgebraicRingHomExt.eq _ _ (ringHom_eq p X Y f hp n α)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientFrameNaturality.IntrinsicPadicQuotientFrameNaturality
