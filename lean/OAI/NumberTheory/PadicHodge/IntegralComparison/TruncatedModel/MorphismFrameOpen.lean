import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameSource
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismSectionMap

/-! # Morphism Frame Open -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameOpen

noncomputable section

/-! The original native frame comparison is geometrically natural
on both variables of the compatible-affine-pair section diagram. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p] (n : ℕ)
  {X₁ X₂ : Over (Spec (CommRingCat.of (Truncated.Witt.Ring p k n)))} [Smooth X₁.hom] [Smooth X₂.hom]
  {Y₁ Y₂ : Over (Spec (CommRingCat.of k))} [IsSeparated Y₁.hom] [IsSeparated Y₂.hom]
  (u : X₁ ⟶ X₂) (v : Y₁ ⟶ Y₂) (f₁ : Y₁.left ⟶ X₁.left) (f₂ : Y₂.left ⟶ X₂.left)
  (hp₁ : IsPullback f₁ Y₁.hom X₁.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (hp₂ : IsPullback f₂ Y₂.hom X₂.hom (Spec.map (CommRingCat.ofHom (Truncated.Witt.reduction p k n))))
  (sq : f₁ ≫ u.left = v.left ≫ f₂)

open OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismData.Frames
local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "w₁" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₁
local notation "w₂" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y₂
local notation "P" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.source (Over.Hom.left u) ⋙ OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor.functor p k n X₁ Y₁ f₁ hp₁
local notation "Q" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.target (Over.Hom.left u) ⋙ OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FrameFunctor.functor p k n X₂ Y₂ f₂ hp₂
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismDiagram.transformation p k n u v f₁ f₂ hp₁ hp₂ sq

local instance sourceSeparated : IsSeparated w₁ := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance
local instance targetSeparated : IsSeparated w₂ := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance constPairsZero :
    (Functor.const (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ : ModuleCat.{2} Rcoeff ⥤
      (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} Rcoeff).PreservesZeroMorphisms where
  map_zero _ _ := rfl
local instance constSourceZero :
    (Functor.const Y₁.left.Opensᵒᵖ : ModuleCat.{2} Rcoeff ⥤ Y₁.left.Opensᵒᵖ ⥤ ModuleCat.{2} Rcoeff).PreservesZeroMorphisms where
  map_zero _ _ := rfl
local instance constTargetZero :
    (Functor.const Y₂.left.Opensᵒᵖ : ModuleCat.{2} Rcoeff ⥤ Y₂.left.Opensᵒᵖ ⥤ ModuleCat.{2} Rcoeff).PreservesZeroMorphisms where
  map_zero _ _ := rfl

def sourcePullback : (Y₁.left.Opensᵒᵖ ⥤ ModuleCat.{2} Rcoeff) ⥤
    ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} Rcoeff) :=
  (Functor.whiskeringLeft _ _ _).obj (MorphismOpenPairs.source p k n u f₁).op
def targetPullback : (Y₂.left.Opensᵒᵖ ⥤ ModuleCat.{2} Rcoeff) ⥤
    ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} Rcoeff) :=
  (Functor.whiskeringLeft _ _ _).obj (MorphismOpenPairs.target p k n u f₂).op

instance sourcePullback_additive : (sourcePullback p k n u f₁).Additive := by
  dsimp only [sourcePullback]
  infer_instance
instance targetPullback_additive : (targetPullback p k n u f₂).Additive := by
  dsimp only [targetPullback]
  infer_instance

def constantComplexes : CochainComplex (ModuleCat.{2} Rcoeff) ℕ ⥤
    CochainComplex ((AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} Rcoeff) ℕ :=
  (Functor.const (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ : ModuleCat.{2} Rcoeff ⥤
    (AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left)ᵒᵖ ⥤ ModuleCat.{2} Rcoeff).mapHomologicalComplex (.up ℕ)

local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameOpen.constantComplexes p k n u

def sourceOpen : (P).op ⋙ GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality.source w₁ n ⋙ K ⟶
    (P).op ⋙ GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor w₁ n ⋙
      (MorphismSectionMap.sourceSections p k n u f₁).mapHomologicalComplex (.up ℕ) :=
  Functor.whiskerRight (Functor.whiskerLeft (P).op (GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation w₁ n))
    ((sourcePullback p k n u f₁).mapHomologicalComplex (.up ℕ))

def targetOpen : (Q).op ⋙ GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality.source w₂ n ⋙ K ⟶
    (Q).op ⋙ GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor w₂ n ⋙
      (MorphismSectionMap.targetSections p k n u f₂).mapHomologicalComplex (.up ℕ) :=
  Functor.whiskerRight (Functor.whiskerLeft (Q).op (GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation w₂ n))
    ((targetPullback p k n u f₂).mapHomologicalComplex (.up ℕ))

omit [IsSeparated Y₁.hom] [IsSeparated Y₂.hom] in
theorem frame_component (U : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left) :
    (MorphismFrameSource.transformation p k n u v f₁ f₂ hp₁ hp₂ sq).app (op U) =
      ((ModuleCat.uliftFunctor.{2, 1} Rcoeff).mapHomologicalComplex (.up ℕ)).map
        (BoundedFrame.SectionChange.frameMap ((a).app U)) :=
  MorphismFrameSource.component p k n u v f₁ f₂ hp₁ hp₂ sq U

theorem component (F U : AlgebraicGeometry.Crystalline.Cohomology.Affine.MorphismPairs.AffineMorphismPairs.Charts u.left) (i : ℕ) :
    (((targetOpen p k n u f₂ hp₂).app (op F)).f i).app (op U) ≫
      (((MorphismSectionMap.complexes p k n u v f₁ f₂ sq hp₁ hp₂).app (op F)).f i).app (op U) =
    ((MorphismFrameSource.transformation p k n u v f₁ f₂ hp₁ hp₂ sq).app (op F)).f i ≫
      (((sourceOpen p k n u f₁ hp₁).app (op F)).f i).app (op U) := by
  have h := GeometricComparison.Frame.OpenRestriction.FrameGeometricOpenRestriction.natural v.left (MorphismData.Frames.ambient_over p k v) n ((a).app F)
    (f₂ ⁻¹ᵁ U.val.2.val) (f₁ ⁻¹ᵁ U.val.1.val)
    (AlgebraicGeometry.Crystalline.Cohomology.OpenSectionGeometricPullback.SectionGeometricSquare.preimage_le u.left v.left f₁ f₂ sq
      U.val.2.val U.val.1.val U.property) i
  have hc := congrArg (fun q => q.f i) (frame_component p k n u v f₁ f₂ hp₁ hp₂ sq F)
  exact h.trans (congrArg (fun q => q ≫
    (((GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation w₁ n).app (op ((P).obj F))).f i).app
      (op (f₁ ⁻¹ᵁ U.val.1.val))) hc.symm)

/-- Restrict the target frame comparison along the original section map. -/
def naturalityLeft := targetOpen p k n u f₂ hp₂ ≫
  MorphismSectionMap.complexes p k n u v f₁ f₂ sq hp₁ hp₂

/-- Apply the frame map before the source open comparison. -/
def naturalityRight :=
  Functor.whiskerRight (MorphismFrameSource.transformation p k n u v f₁ f₂ hp₁ hp₂ sq) K ≫
    sourceOpen p k n u f₁ hp₁

theorem natural : naturalityLeft p k n u v f₁ f₂ hp₁ hp₂ sq =
    naturalityRight p k n u v f₁ f₂ hp₁ hp₂ sq := by
  apply NatTrans.ext
  funext F
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext U
  exact component p k n u v f₁ f₂ hp₁ hp₂ sq F.unop U.unop i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.MorphismFrameOpen
