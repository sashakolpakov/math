import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebra
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedDeRhamMap

/-! # Reduced Source -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedSource.IntrinsicPadicGeometricReducedSource

noncomputable section

/-! Actual integral pullback induces the original de Rham coefficient
quotient map on every compatible affine source and target pair. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  {X Y : Over (Spec (CommRingCat.of ℤ_[p]))} [Smooth X.hom] [Smooth Y.hom]
  (u : X ⟶ Y) (n : ℕ)

local notation "W" => WittVector p (ZMod p)
local notation "Ip" => (Ideal.span {(p : WittVector p (ZMod p))}) ^ (n + 1)

def transformation : (Affine.MapPairs.AffineMapPairs.target u.left).op ⋙ ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.source p Y n ⟶
    (Affine.MapPairs.AffineMapPairs.source u.left).op ⋙ ReducedDeRhamMap.IntrinsicPadicReducedDeRhamMap.source p X n :=
  Functor.whiskerRight (IntegralAlgebra.IntrinsicPadicGeometricIntegralAlgebra.transformation p u)
    (IntegralComparison.OrdinaryDeRhamFunctor.Ordinary.functor W ⋙
      (IntegralComparison.Module.IdealQuotient.functor W Ip).mapHomologicalComplex (.up ℕ))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.ReducedSource.IntrinsicPadicGeometricReducedSource
