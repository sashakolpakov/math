import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor

/-! # Frame Functor Map -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctorMap.IntrinsicPadicFrameFunctorMap

/-! The strict native frame functor uses exactly the original restriction morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

theorem map_eq {I J : X.left.affineOpens} (α : I ⟶ J) :
    (FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp n).map α =
      PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp I.val J.val I.property J.property (leOfHom α) n := rfl

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctorMap.IntrinsicPadicFrameFunctorMap

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctorMap.IntrinsicPadicFrameFunctorRingMap

/-! The native functor restriction identity on the underlying ring homomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

theorem map_eq {I J : X.left.affineOpens} (α : I ⟶ J) :
    ((FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp n).map α).hom.ringMap.toRingHom =
      (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp I.val J.val I.property J.property (leOfHom α) n).hom.ringMap.toRingHom :=
  congrArg (fun m => m.hom.ringMap.toRingHom) (IntrinsicPadicFrameFunctorMap.map_eq p X Y f hp n α)

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctorMap.IntrinsicPadicFrameFunctorRingMap

end

end OAI
