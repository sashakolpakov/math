import OAI.NumberTheory.PadicHodge.IntegralComparison.GlobalFunction.WittFactor

/-! # Global Function Scheme -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.GlobalFunctionScheme

noncomputable section

/-! The canonical affine presentation by global functions is an isomorphism over the original field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (k : Type u) [Field k] (X : Over (Spec (CommRingCat.of k))) [IsAffine X.left]

def iso : X ≅ Crystalline.Presentation.affineScheme k
    (SmoothProper.GlobalFunctionAlgebra.algebra k X) :=
  Over.isoMk X.left.isoSpec (GlobalFunction.WittFactor.affinization_overBase k X)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Affine.GlobalFunctionScheme
