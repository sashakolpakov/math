import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.RestrictionLaws

/-! # Integral Algebra Functor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor

noncomputable section

/-! The actual integral affine sections form a Witt-algebra-valued
contravariant functor using their original restriction maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime] (X : Over (Spec (CommRingCat.of ℤ_[p])))
local notation "W" => WittVector p (ZMod p)
local instance padic (I : X.left.affineOpens) : Algebra ℤ_[p] (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X I.val) :=
  AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra ℤ_[p] X I.val
local instance witt (I : X.left.affineOpens) : Algebra W (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X I.val) :=
  WittAlgebra.PadicWittAlgebra.algebra p (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X I.val)

def functor : X.left.affineOpensᵒᵖ ⥤ CommAlgCat W where
  obj I := CommAlgCat.of W (AffineFrame.IntrinsicPadicAffineFrame.sourceRing p X I.unop.val)
  map {I J} α := CommAlgCat.ofHom
    (FrameRestrictionData.IntrinsicPadicFrameRestrictionData.integralMap p X J.unop.val I.unop.val (leOfHom α.unop))
  map_id I := by
    ext a
    exact RestrictionLaws.IntrinsicPadicRestrictionLaws.id p X I.unop.val a
  map_comp {I J K} α β := by
    ext a
    exact RestrictionLaws.IntrinsicPadicRestrictionLaws.comp p X K.unop.val J.unop.val I.unop.val
      (leOfHom β.unop) (leOfHom α.unop) a

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor
