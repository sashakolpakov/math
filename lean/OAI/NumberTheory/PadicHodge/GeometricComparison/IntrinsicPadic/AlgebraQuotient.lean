import OAI.NumberTheory.PadicHodge.GeometricComparison.PrimePowerId
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralAlgebraFunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.FrameRingFunctor

/-! # Algebra Quotient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AlgebraQuotient.IntrinsicPadicAlgebraQuotient

noncomputable section

/-! The native integral algebra diagram has its canonical prime-power
quotient diagram independently of the crystalline presentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime] (X : Over (Spec (CommRingCat.of ℤ_[p]))) (n : ℕ)

def functor := IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X ⋙
  PrimePowerId.PrimePowerAlgebraQuotient.functor (WittVector p (ZMod p)) p n

def reduction : IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X ⟶ functor p X n :=
  Functor.whiskerLeft (IntegralAlgebraFunctor.IntrinsicPadicIntegralAlgebraFunctor.functor p X)
    (PrimePowerId.PrimePowerAlgebraQuotient.reduction (WittVector p (ZMod p)) p n)

variable [Smooth X.hom] (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))

def frameIso (I : X.left.affineOpens) : (functor p X n).obj (op I) ≅
    (Crystalline.FrameRingFunctor.CrystallineFrameRingFunctor.bounded (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n).obj
      (op (ChartImage.IntrinsicPadicOpenFrame.frame p X Y f hp I.val I.property n)) := Iso.refl _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.AlgebraQuotient.IntrinsicPadicAlgebraQuotient
