import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AlgebraQuotient
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ProjectionNaturality

/-! # Local Quotient Map -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.LocalQuotientMap.IntrinsicPadicQuotientFrameCoordinates

/-! Generator coordinates of the proved native quotient/frame algebra isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) (n : ℕ)

def mk (I : X.left.affineOpens) :
    (IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X).obj (op I) →+*
      (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.functor p X n).obj (op I) :=
  ((AlgebraQuotient.IntrinsicPadicAlgebraQuotient.reduction p X n).app (op I)).hom.toRingHom

theorem mk_surjective (I : X.left.affineOpens) : Function.Surjective (mk p X n I) :=
  Ideal.Quotient.mk_surjective

theorem map_mk {I J : X.left.affineOpens} (α : I ⟶ J)
    (a : (IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X).obj (op J)) :
    ((AlgebraQuotient.IntrinsicPadicAlgebraQuotient.functor p X n).map α.op).hom.toRingHom (mk p X n J a) =
      mk p X n I (((IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X).map α.op).hom a) := rfl

variable [Smooth X.hom] (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))

theorem hom_mk (I : X.left.affineOpens)
    (a : (IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X).obj (op I)) :
    (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp I).hom.hom (mk p X n I a) =
      ProjectionNaturality.IntrinsicPadicProjectionNaturality.projection p X Y f hp n I a := rfl

theorem inv_mk (I : X.left.affineOpens)
    (a : (IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X).obj (op I)) :
    (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp I).inv.hom
      (ProjectionNaturality.IntrinsicPadicProjectionNaturality.projection p X Y f hp n I a) = mk p X n I a := rfl

theorem hom_ring_mk (I : X.left.affineOpens)
    (a : (IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X).obj (op I)) :
    (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp I).hom.hom.toRingHom (mk p X n I a) =
      ProjectionNaturality.IntrinsicPadicProjectionNaturality.projection p X Y f hp n I a := rfl

theorem inv_ring_mk (I : X.left.affineOpens)
    (a : (IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X).obj (op I)) :
    (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp I).inv.hom.toRingHom
      (ProjectionNaturality.IntrinsicPadicProjectionNaturality.projection p X Y f hp n I a) = mk p X n I a := rfl

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.LocalQuotientMap.IntrinsicPadicQuotientFrameCoordinates

namespace NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.LocalQuotientMap.IntrinsicPadicLocalQuotientMap

/-! The unpostcomposed native frame restriction is the canonical quotient map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

theorem raw_to_local {I J : X.left.affineOpens} (α : I ⟶ J) :
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp
      I.val J.val I.property J.property (leOfHom α) n).hom.ringMap.toRingHom =
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.localMap p X Y f hp
      I.val J.val I.property J.property (leOfHom α) n).hom.ringMap.toRingHom :=
  congrArg DividedPowers.DPMorphism.toRingHom
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map_ringMap p X Y f hp
      I.val J.val I.property J.property (leOfHom α) n)

theorem local_formula {I J : X.left.affineOpens} (α : I ⟶ J) :
    (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp I).inv.hom.toRingHom.comp
      ((PadicFrameRestriction.IntrinsicPadicFrameRestriction.localMap p X Y f hp
        I.val J.val I.property J.property (leOfHom α) n).hom.ringMap.toRingHom.comp
          (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp J).hom.hom.toRingHom) =
    ((AlgebraQuotient.IntrinsicPadicAlgebraQuotient.functor p X n).map α.op).hom.toRingHom := rfl

end NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.LocalQuotientMap.IntrinsicPadicLocalQuotientMap

end

end OAI
