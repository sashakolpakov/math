import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctorMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebraFunctor

/-! # Projection Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ProjectionNaturality.IntrinsicPadicProjectionNaturality

noncomputable section

/-! The native projection square, split at the underlying ring-homomorphism level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp n
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X

local instance padic (I : X.left.affineOpens) : Algebra ℤ_[p] (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X I.val) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X I.val
local instance witt (I : X.left.affineOpens) : Algebra (WittVector p (ZMod p)) (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X I.val) :=
  WittAlgebra.PadicWittAlgebra.algebra p (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X I.val)

def projection (I : X.left.affineOpens) :
    AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X I.val →+* (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp I.val I.property n).obj.ring :=
  Ideal.Quotient.mk ((Ideal.span {(p : AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X I.val)}) ^ (n + 1))

theorem projection_apply (I : X.left.affineOpens) (a : AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X I.val) :
    projection p X Y f hp n I a = FrameGenerators.IntrinsicPadicFrameGenerators.generators p X Y f hp n I.val I.property a := rfl

theorem restriction_apply {I J : X.left.affineOpens} (α : I ⟶ J)
    (a : AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X J.val) :
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp I.val J.val I.property J.property (leOfHom α) n).hom.ringMap.toRingHom
      (projection p X Y f hp n J a) =
    projection p X Y f hp n I (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X I.val J.val (leOfHom α) a) := by
  exact (DividedPowers.DPMorphism.toRingHom_apply _ _).trans ((congrArg (fun b =>
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp I.val J.val I.property J.property (leOfHom α) n).hom.ringMap b)
    (projection_apply p X Y f hp n J a)).trans
      ((FrameGenerators.IntrinsicPadicFrameGenerators.map p X Y f hp n I.val J.val I.property J.property (leOfHom α) a).trans
        (projection_apply p X Y f hp n I _).symm))

omit [Smooth X.hom] in
theorem integral_map {I J : X.left.affineOpens} (α : I ⟶ J) :
    ((A).map α.op).hom.toRingHom =
      (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X I.val J.val (leOfHom α)).toRingHom := rfl

theorem natural {I J : X.left.affineOpens} (α : I ⟶ J) (a : (A).obj (op J)) :
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp I.val J.val I.property J.property (leOfHom α) n).hom.ringMap.toRingHom
      (projection p X Y f hp n J a) =
    projection p X Y f hp n I (((A).map α.op).hom a) :=
  (restriction_apply p X Y f hp n α a).trans
    (congrArg (fun b => projection p X Y f hp n I b) (RingHom.congr_fun (integral_map p X α).symm a))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ProjectionNaturality.IntrinsicPadicProjectionNaturality
