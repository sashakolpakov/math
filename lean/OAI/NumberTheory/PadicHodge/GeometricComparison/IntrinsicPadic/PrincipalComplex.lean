import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameBaseIdeal
import OAI.NumberTheory.PadicHodge.GeometricComparison.PrincipalFrameComplex

/-! # Principal Complex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison

noncomputable section

/-! The actual native divided-power frame diagram is naturally isomorphic
to the ordinary de Rham diagram of its ambient prime-power quotient rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "N" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp n

def frames := (N).op ⋙ (IntegralComparison.BoundedCrystalline.Site.inclusion w n).op

def rings : X.left.affineOpensᵒᵖ ⥤ CommAlgCat W :=
  (N).op ⋙ Crystalline.FrameRingFunctor.CrystallineFrameRingFunctor.bounded w n

def pdComplexes : X.left.affineOpensᵒᵖ ⥤ CochainComplex (ModuleCat W) ℕ :=
  (N).op ⋙ Crystalline.FrameComplexFunctor.CrystallineFrameComplexFunctor.bounded w n

def ordinaryComplexes : X.left.affineOpensᵒᵖ ⥤ CochainComplex (ModuleCat W) ℕ :=
  rings p X Y f hp n ⋙ IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor W

theorem ideal_generated (I : X.left.affineOpensᵒᵖ) :
    ((frames p X Y f hp n).obj I).unop.ideal =
      Ideal.span {((frames p X Y f hp n).obj I).unop.base (p : W)} :=
  (FrameBaseIdeal.IntrinsicPadicFrameCartesian.ideal_eq_span p X Y f hp n I.unop.val I.unop.property).trans
    (congrArg (fun a => Ideal.span {a})
      (map_natCast ((frames p X Y f hp n).obj I).unop.base p).symm)

def iso : pdComplexes p X Y f hp n ≅ ordinaryComplexes p X Y f hp n :=
  PrincipalFrameComplex.PrincipalFrameComplexComparison.iso (p : W) γ w (frames p X Y f hp n)
    (ideal_generated p X Y f hp n)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison
