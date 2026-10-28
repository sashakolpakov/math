import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.QuotientFrameNaturalIso
import OAI.NumberTheory.PadicHodge.GeometricComparison.OrdinaryDeRhamDiagram

/-! # Reduced De Rham Map -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap

noncomputable section

/-! The original integral Witt de Rham coefficient quotients map naturally
into the actual native PD-frame complex diagram at each finite level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "Ip" => (Ideal.span {(p : WittVector p (ZMod p))}) ^ (n + 1)
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X
local notation "B" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.rings p X Y f hp n

def source : X.left.affineOpensᵒᵖ ⥤ CochainComplex (ModuleCat W) ℕ :=
  A ⋙ IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor W ⋙
    (IntegralComparison.Module.IdealQuotient.functor W Ip).mapHomologicalComplex (.up ℕ)

def ordinaryTransformation : source p X n ⟶
    PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.ordinaryComplexes p X Y f hp n :=
  OrdinaryDeRhamDiagram.OrdinaryDeRhamReductionDiagram.transformation W Ip A B
    (QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.transformation p X Y f hp n)
    (QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.annihilation p X Y f hp n)

def pdTransformation : source p X n ⟶
    PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.pdComplexes p X Y f hp n :=
  ordinaryTransformation p X Y f hp n ≫ (PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.iso p X Y f hp n).inv

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap
