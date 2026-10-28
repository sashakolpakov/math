import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameSource
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionMap

/-! # Frame Open -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameOpen.IntrinsicPadicGeometricFrameOpen

noncomputable section

/-! The original native frame comparison is geometrically natural
on both variables of the compatible-affine-pair section diagram. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  {X₁ X₂ : Over (Spec (CommRingCat.of ℤ_[p]))} [Smooth X₁.hom] [Smooth X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of (ZMod p)))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (hsquare : f₁ ≫ u.left = v.left ≫ f₂) (n : ℕ)

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameData.IntrinsicPadicFrameGeometricData
local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y₂
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.source (Over.Hom.left u) ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X₁ Y₁ f₁ hp₁ n
local notation "Q" => OAI.NumberTheory.PadicHodge.GeometricComparison.Affine.MapPairs.AffineMapPairs.target (Over.Hom.left u) ⋙ OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X₂ Y₂ f₂ hp₂ n
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameDiagram.IntrinsicPadicFrameGeometricDiagram.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n

local instance sourceSeparated : IsSeparated w₁ := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance
local instance targetSeparated : IsSeparated w₂ := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

local instance constPairsZero :
    (Functor.const (Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ : ModuleCat.{2} Rcoeff ⥤
      (Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} Rcoeff).PreservesZeroMorphisms where
  map_zero _ _ := rfl
local instance constSourceZero :
    (Functor.const Y₁.left.Opensᵒᵖ : ModuleCat.{2} Rcoeff ⥤ Y₁.left.Opensᵒᵖ ⥤ ModuleCat.{2} Rcoeff).PreservesZeroMorphisms where
  map_zero _ _ := rfl
local instance constTargetZero :
    (Functor.const Y₂.left.Opensᵒᵖ : ModuleCat.{2} Rcoeff ⥤ Y₂.left.Opensᵒᵖ ⥤ ModuleCat.{2} Rcoeff).PreservesZeroMorphisms where
  map_zero _ _ := rfl

def sourcePullback : (Y₁.left.Opensᵒᵖ ⥤ ModuleCat.{2} Rcoeff) ⥤
    ((Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} Rcoeff) :=
  (Functor.whiskeringLeft _ _ _).obj (OpenPairs.IntrinsicPadicGeometricOpenPairs.source p u f₁).op
def targetPullback : (Y₂.left.Opensᵒᵖ ⥤ ModuleCat.{2} Rcoeff) ⥤
    ((Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} Rcoeff) :=
  (Functor.whiskeringLeft _ _ _).obj (OpenPairs.IntrinsicPadicGeometricOpenPairs.target p u f₂).op

instance sourcePullback_additive : (sourcePullback p u f₁).Additive := by
  dsimp only [sourcePullback]
  infer_instance
instance targetPullback_additive : (targetPullback p u f₂).Additive := by
  dsimp only [targetPullback]
  infer_instance

def constantComplexes : CochainComplex (ModuleCat.{2} Rcoeff) ℕ ⥤
    CochainComplex ((Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} Rcoeff) ℕ :=
  (Functor.const (Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ : ModuleCat.{2} Rcoeff ⥤
    (Affine.MapPairs.AffineMapPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} Rcoeff).mapHomologicalComplex (.up ℕ)

local notation "K" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameOpen.IntrinsicPadicGeometricFrameOpen.constantComplexes p u

def sourceOpen : (P).op ⋙ Frame.OpenSectionNaturality.FrameOpenSectionNaturality.source w₁ n ⋙ K ⟶
    (P).op ⋙ BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor w₁ n ⋙
      (SectionMap.IntrinsicPadicGeometricSectionMap.sourceSections p u f₁ n).mapHomologicalComplex (.up ℕ) :=
  Functor.whiskerRight (Functor.whiskerLeft (P).op (Frame.OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation w₁ n))
    ((sourcePullback p u f₁).mapHomologicalComplex (.up ℕ))

def targetOpen : (Q).op ⋙ Frame.OpenSectionNaturality.FrameOpenSectionNaturality.source w₂ n ⋙ K ⟶
    (Q).op ⋙ BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor w₂ n ⋙
      (SectionMap.IntrinsicPadicGeometricSectionMap.targetSections p u f₂ n).mapHomologicalComplex (.up ℕ) :=
  Functor.whiskerRight (Functor.whiskerLeft (Q).op (Frame.OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation w₂ n))
    ((targetPullback p u f₂).mapHomologicalComplex (.up ℕ))

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem frame_component (U : Affine.MapPairs.AffineMapPairs.Charts u.left) :
    (FrameSource.IntrinsicPadicGeometricFrameSource.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n).app (op U) =
      ((ModuleCat.uliftFunctor.{2, 1} Rcoeff).mapHomologicalComplex (.up ℕ)).map
        (IntegralComparison.BoundedFrame.SectionChange.frameMap ((a).app U)) :=
  FrameSource.IntrinsicPadicGeometricFrameSource.component p u v f₁ f₂ hp₁ hp₂ hsquare n U

theorem component (F U : Affine.MapPairs.AffineMapPairs.Charts u.left) (i : ℕ) :
    (((targetOpen p u f₂ hp₂ n).app (op F)).f i).app (op U) ≫
      (((SectionMap.IntrinsicPadicGeometricSectionMap.complexes p u v f₁ f₂ hsquare n hp₁ hp₂).app (op F)).f i).app (op U) =
    ((FrameSource.IntrinsicPadicGeometricFrameSource.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n).app (op F)).f i ≫
      (((sourceOpen p u f₁ hp₁ n).app (op F)).f i).app (op U) := by
  have h := Frame.OpenRestriction.FrameGeometricOpenRestriction.natural v.left (FrameData.IntrinsicPadicFrameGeometricData.global_over_witt p v) n ((a).app F)
    (f₂ ⁻¹ᵁ U.val.2.val) (f₁ ⁻¹ᵁ U.val.1.val)
    (Section.GeometricRestriction.SectionGeometricSquare.preimage_le u.left v.left f₁ f₂ hsquare
      U.val.2.val U.val.1.val U.property) i
  have hc := congrArg (fun q => q.f i) (frame_component p u v f₁ f₂ hp₁ hp₂ hsquare n F)
  exact h.trans (congrArg (fun q => q ≫
    (((Frame.OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation w₁ n).app (op ((P).obj F))).f i).app
      (op (f₁ ⁻¹ᵁ U.val.1.val))) hc.symm)

/-- Restrict the target frame comparison along the original section map. -/
def naturalityLeft := targetOpen p u f₂ hp₂ n ≫
  SectionMap.IntrinsicPadicGeometricSectionMap.complexes p u v f₁ f₂ hsquare n hp₁ hp₂

/-- Apply the frame map before the source open comparison. -/
def naturalityRight :=
  Functor.whiskerRight (FrameSource.IntrinsicPadicGeometricFrameSource.transformation p u v f₁ f₂ hp₁ hp₂ hsquare n) K ≫
    sourceOpen p u f₁ hp₁ n

theorem natural : naturalityLeft p u v f₁ f₂ hp₁ hp₂ hsquare n =
    naturalityRight p u v f₁ f₂ hp₁ hp₂ hsquare n := by
  apply NatTrans.ext
  funext F
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext U
  exact component p u v f₁ f₂ hp₁ hp₂ hsquare n F.unop U.unop i

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameOpen.IntrinsicPadicGeometricFrameOpen
