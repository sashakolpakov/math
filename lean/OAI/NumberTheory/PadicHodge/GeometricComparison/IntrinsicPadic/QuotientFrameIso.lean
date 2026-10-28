import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.LocalQuotientMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.ConjugateRingMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraicConjugateByGenerators

/-! # Quotient Frame Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientFrameIso.IntrinsicPadicQuotientFrameIso

noncomputable section

/-! Naturality of the componentwise identification of native quotient algebras
with the original crystalline frame algebras. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "quotients" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AlgebraQuotient.IntrinsicPadicAlgebraQuotient.functor p X n
local notation "ambient" => OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameRingFunctor.CrystallineFrameRingFunctor.bounded
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n

def conjugatedMap {I J : X.left.affineOpens} (α : I ⟶ J) :
    (quotients).obj (op J) ⟶ (quotients).obj (op I) :=
  (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp J).hom ≫
    (ambient).map (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp
      I.val J.val I.property J.property (leOfHom α) n).op ≫
      (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp I).inv

theorem conjugatedMap_ringHom {I J : X.left.affineOpens} (α : I ⟶ J) :
    (conjugatedMap p X Y f hp n α).hom.toRingHom =
      (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp I).inv.hom.toRingHom.comp
        ((PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp
          I.val J.val I.property J.property (leOfHom α) n).hom.ringMap.toRingHom.comp
            (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp J).hom.hom.toRingHom) :=
  Crystalline.ConjugateRingMap.CrystallineConjugateRingMap.ringHom (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp I.val J.val I.property J.property (leOfHom α) n)
    (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp J)
    (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp I)

theorem raw_generator_apply {I J : X.left.affineOpens} (α : I ⟶ J)
    (a : (IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X).obj (op J)) :
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp
      I.val J.val I.property J.property (leOfHom α) n).hom.ringMap.toRingHom
        ((AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp J).hom.hom.toRingHom
          (LocalQuotientMap.IntrinsicPadicQuotientFrameCoordinates.mk p X n J a)) =
    ProjectionNaturality.IntrinsicPadicProjectionNaturality.projection p X Y f hp n I
      (((IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X).map α.op).hom a) := by
  rw [LocalQuotientMap.IntrinsicPadicQuotientFrameCoordinates.hom_ring_mk]
  exact ProjectionNaturality.IntrinsicPadicProjectionNaturality.natural p X Y f hp n α a

theorem inv_generator_apply {I J : X.left.affineOpens} (α : I ⟶ J)
    (a : (IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X).obj (op J)) :
    (AlgebraQuotient.IntrinsicPadicAlgebraQuotient.frameIso p X n Y f hp I).inv.hom.toRingHom
      (ProjectionNaturality.IntrinsicPadicProjectionNaturality.projection p X Y f hp n I
        (((IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X).map α.op).hom a)) =
    ((quotients).map α.op).hom.toRingHom (LocalQuotientMap.IntrinsicPadicQuotientFrameCoordinates.mk p X n J a) :=
  (LocalQuotientMap.IntrinsicPadicQuotientFrameCoordinates.inv_ring_mk p X n Y f hp I _).trans
    (LocalQuotientMap.IntrinsicPadicQuotientFrameCoordinates.map_mk p X n α a).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientFrameIso.IntrinsicPadicQuotientFrameIso
