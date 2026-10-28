import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.OrdinaryReductionProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.FrameComplexInverseProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Frame.DiagramProduct

/-! # Reduced Product -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ReducedProduct.Intrinsic

noncomputable section

/-! The literal coefficient-quotient map in the existing p-adic
comparison preserves the actual integral/PD products in every degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom
    (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p)))) (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "Ip" => (Ideal.span {(p : W)}) ^ (n+1)
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)
local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.frames p X Y f hp n
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.source p X n
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.pdTransformation p X Y f hp n

def pairing (i j : ℕ) (V : X.left.affineOpensᵒᵖ) :
    ((P).obj V).X i →ₗ[W] ((P).obj V).X j →ₗ[W] ((P).obj V).X (i+j) :=
  OrdinaryReductionProduct.Geometric.OrdinaryDeRhamCoefficientReduction.quotientPairing W Ip ((A).obj V) i j

theorem map_pairing (i j : ℕ) (V : X.left.affineOpensᵒᵖ)
    (x : ((P).obj V).X i) (y : ((P).obj V).X j) :
    ((a).app V).f (i+j) (pairing p X n i j V x y) =
      Frame.DiagramProduct.pairing w H i j V
        (((a).app V).f i x) (((a).app V).f j y) := by
  let b := GeometricComparison.OrdinaryDeRhamIs.OrdinaryDeRhamCoefficientReduction.map W Ip
    ((GeometricComparison.IntrinsicPadic.QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.transformation p X Y f hp n).app V)
    (GeometricComparison.IntrinsicPadic.QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.annihilation p X Y f hp n V)
  let e := GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.iso p X Y f hp n
  change (e.inv.app V).f (i+j) (b.f (i+j) (pairing p X n i j V x y)) = _
  exact (congrArg (fun z => (e.inv.app V).f (i+j) z)
    (OrdinaryReductionProduct.Geometric.OrdinaryDeRhamCoefficientReduction.map_wedge W Ip
      ((GeometricComparison.IntrinsicPadic.QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.transformation p X Y f hp n).app V)
      (GeometricComparison.IntrinsicPadic.QuotientFrameNaturalIso.IntrinsicPadicQuotientRingMap.annihilation p X Y f hp n V) i j x y)).trans
    (Principal.FrameComplexInverseProduct.inv_wedge (p : W) γ w H
      (GeometricComparison.IntrinsicPadic.PrincipalComplex.IntrinsicPadicPrincipalComplexComparison.ideal_generated p X Y f hp n) V i j
      (b.f i x) (b.f j y))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.IntrinsicPadic.ReducedProduct.Intrinsic
