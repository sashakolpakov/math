import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrobeniusFrameComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjective
import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameFrobeniusCoefficientForms

/-! # Frobenius Frame Source -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusFrameSource.IntrinsicPadicFrobeniusFrameSource

noncomputable section

/-! Actual frame Frobenius acts on the native large-coefficient
frame-source diagram and is zero in every positive form degree. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))

def transformation : FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.source p X Y f hp 0 ⟶
    FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.source p X Y f hp 0 :=
  Functor.whiskerRight
    (Functor.whiskerLeft (FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp 0).op
      (LevelZero.FrobeniusFrameComplex.LevelZeroFrobeniusFrameComplex.transformation p Y))
    ((IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.coefficients p).mapHomologicalComplex (.up ℕ))

omit [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem component (U : X.left.affineOpens) : (transformation p X Y f hp).app (op U) =
    ((ModuleCat.uliftFunctor.{2, 1} R).mapHomologicalComplex (.up ℕ)).map
      (IntegralComparison.BoundedFrame.SectionChange.frameMap (LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.map p Y
        ((FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp 0).obj U))) := by
  change ((IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.coefficients p).mapHomologicalComplex (.up ℕ)).map
    ((LevelZero.FrobeniusFrameComplex.LevelZeroFrobeniusFrameComplex.pulled p Y).app
      (op ((FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp 0).obj U)) ≫ 𝟙 _) = _
  rw [Category.comp_id]
  rfl

omit [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem positive (U : X.left.affineOpens) (n : ℕ) (hn : 0 < n) :
    ((transformation p X Y f hp).app (op U)).f n = 0 := by
  rw [component]
  exact LevelZero.FrameFrobeniusCoefficientForms.LevelZeroFrameFrobeniusCoefficientForms.positive p Y
    ((FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp 0).obj U) n hn

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusFrameSource.IntrinsicPadicFrobeniusFrameSource
