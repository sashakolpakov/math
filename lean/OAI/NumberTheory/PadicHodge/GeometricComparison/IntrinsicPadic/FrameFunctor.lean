import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameGenerators
import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.RingExt
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RestrictionLaws

/-! # Frame Functor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor

noncomputable section

/-! Actual affine integral-section frames form a strict functor on affine opens. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

theorem map_id (U : X.left.Opens) (hU : IsAffineOpen U) :
    PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U U hU hU le_rfl n =
      𝟙 (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp U hU n) :=
  BoundedFrame.RingExt.BoundedFrameRingExt.id_of_formula (FrameGenerators.IntrinsicPadicFrameGenerators.generators p X Y f hp n U hU)
    (FrameGenerators.IntrinsicPadicFrameGenerators.surjective p X Y f hp n U hU)
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U U hU hU le_rfl n)
    (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X U U le_rfl)
    (FrameGenerators.IntrinsicPadicFrameGenerators.map p X Y f hp n U U hU hU le_rfl)
    (RestrictionLaws.IntrinsicPadicRestrictionLaws.id p X U)

theorem map_comp (U V T : X.left.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hT : IsAffineOpen T) (hUV : U ≤ V) (hVT : V ≤ T) :
    PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U T hU hT (hUV.trans hVT) n =
      PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV n ≫
        PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp V T hV hT hVT n :=
  BoundedFrame.RingExt.BoundedFrameRingExt.comp_of_formulas
    (FrameGenerators.IntrinsicPadicFrameGenerators.generators p X Y f hp n U hU)
    (FrameGenerators.IntrinsicPadicFrameGenerators.generators p X Y f hp n V hV)
    (FrameGenerators.IntrinsicPadicFrameGenerators.generators p X Y f hp n T hT)
    (FrameGenerators.IntrinsicPadicFrameGenerators.surjective p X Y f hp n T hT)
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U V hU hV hUV n)
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp V T hV hT hVT n)
    (PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U T hU hT (hUV.trans hVT) n)
    (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X U V hUV)
    (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X V T hVT)
    (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X U T (hUV.trans hVT))
    (FrameGenerators.IntrinsicPadicFrameGenerators.map p X Y f hp n U V hU hV hUV)
    (FrameGenerators.IntrinsicPadicFrameGenerators.map p X Y f hp n V T hV hT hVT)
    (FrameGenerators.IntrinsicPadicFrameGenerators.map p X Y f hp n U T hU hT (hUV.trans hVT))
    (RestrictionLaws.IntrinsicPadicRestrictionLaws.comp p X U V T hUV hVT)

def functor : X.left.affineOpens ⥤ IntegralComparison.BoundedCrystalline.Site.Objects (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n where
  obj U := ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp U.val U.property n
  map {U V} α := PadicFrameRestriction.IntrinsicPadicFrameRestriction.map p X Y f hp U.val V.val U.property V.property (leOfHom α) n
  map_id U := IntrinsicPadicFrameFunctor.map_id p X Y f hp n U.val U.property
  map_comp {U V T} α β := IntrinsicPadicFrameFunctor.map_comp p X Y f hp n U.val V.val T.val U.property V.property T.property
    (leOfHom α) (leOfHom β)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor
