import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebraFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs

/-! # Integral Algebra -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebra.IntrinsicPadicGeometricIntegralAlgebra

noncomputable section

/-! Actual integral section-ring pullback is a natural transformation
on compatible affine pairs, with the original Witt algebra structures. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  {X Y : Over (Spec (CommRingCat.of ℤ_[p]))} (u : X ⟶ Y)

def transformation : (Affine.MapPairs.AffineMapPairs.target u.left).op ⋙ IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p Y ⟶
    (Affine.MapPairs.AffineMapPairs.source u.left).op ⋙ IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X where
  app U := by
    let : Algebra ℤ_[p] Γ(X.left, U.unop.val.1.val) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X U.unop.val.1.val
    let : Algebra ℤ_[p] Γ(Y.left, U.unop.val.2.val) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] Y U.unop.val.2.val
    let : Algebra (WittVector p (ZMod p)) Γ(X.left, U.unop.val.1.val) := WittAlgebra.PadicWittAlgebra.algebra p _
    let : Algebra (WittVector p (ZMod p)) Γ(Y.left, U.unop.val.2.val) := WittAlgebra.PadicWittAlgebra.algebra p _
    change CommAlgCat.of (WittVector p (ZMod p)) Γ(Y.left, U.unop.val.2.val) ⟶
      CommAlgCat.of (WittVector p (ZMod p)) Γ(X.left, U.unop.val.1.val)
    exact CommAlgCat.ofHom (FrameData.IntrinsicPadicFrameGeometricData.integralMap p u
      U.unop.val.2.val U.unop.val.1.val U.unop.property)
  naturality U V a := by
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    exact (FrameRestriction.IntrinsicPadicFrameGeometricRestriction.integral_square p u
      V.unop.val.2 U.unop.val.2 V.unop.val.1 U.unop.val.1
      ((Affine.MapPairs.AffineMapPairs.target u.left).map a.unop) ((Affine.MapPairs.AffineMapPairs.source u.left).map a.unop)
      V.unop.property U.unop.property x).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebra.IntrinsicPadicGeometricIntegralAlgebra
