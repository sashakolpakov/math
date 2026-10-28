import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenSectionLevel
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameSourceLevelMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionLevelMap

/-! # Frame Open Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameOpenLevel.IntrinsicPadicFrameOpenLevel

noncomputable section

/-! The original native frame-to-open-section transformation is natural
for the canonical prime-power level maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n m : ℕ) (hnm : n ≤ m)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

local instance separated : IsSeparated wittMap := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

local instance constPreservesZero :
    (Functor.const X.left.affineOpensᵒᵖ : ModuleCat.{2} R ⥤ X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

omit [X.left.IsSeparated] in
theorem natural : FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.openTransformation p X Y f hp m ≫
    SectionLevelMap.IntrinsicPadicSectionLevelMap.complexes p X Y f n m hnm hp =
      Functor.whiskerRight (FrameSourceLevelMap.IntrinsicPadicFrameSourceLevelMap.transformation p X Y f hp n m hnm)
        ((Functor.const X.left.affineOpensᵒᵖ : ModuleCat.{2} R ⥤ X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R).mapHomologicalComplex (.up ℕ)) ≫
          FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.openTransformation p X Y f hp n := by
  apply NatTrans.ext
  funext U
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext V
  exact congrArg (fun q => (q.f i).app ((SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X Y f).op.obj V))
    (Frame.OpenSectionLevel.FrameOpenSectionLevel.natural wittMap n m hnm
      (FrameLevelMap.IntrinsicPadicFrameLevelMap.map p X Y f hp U.unop.val U.unop.property n m hnm))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameOpenLevel.IntrinsicPadicFrameOpenLevel
