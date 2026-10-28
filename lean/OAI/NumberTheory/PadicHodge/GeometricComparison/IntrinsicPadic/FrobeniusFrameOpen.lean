import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameOpenFrobeniusNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusFrameSource
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusSectionMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexWhisker
import OAI.NumberTheory.PadicHodge.GeometricComparison.MappedSquare

/-! # Frobenius Frame Open -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusFrameOpen.IntrinsicPadicFrobeniusFrameOpen

noncomputable section

/-! Reindexing the actual full-frame Frobenius square gives the
native frame-to-open-section square without expanding affine coordinates. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "Frames" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.Objects (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 0
local notation "V" => Functor.op (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrameFunctor.IntrinsicPadicFrameFunctor.functor p X Y f hp 0)
local notation "g" => Over.Hom.left (OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y)
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.over_witt p Y
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) g hg 0
local notation "P" => OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 0
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 0
local notation "O" => OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 0

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

local instance constXZero :
    (Functor.const X.left.affineOpensᵒᵖ : ModuleCat.{2} R ⥤ X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

local instance constYZero :
    (Functor.const Y.left.Opensᵒᵖ : ModuleCat.{2} R ⥤ Y.left.Opensᵒᵖ ⥤ ModuleCat.{2} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

def openPullback : (Y.left.Opensᵒᵖ ⥤ ModuleCat.{2} R) ⥤ (X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) :=
  (Functor.whiskeringLeft X.left.affineOpensᵒᵖ Y.left.Opensᵒᵖ (ModuleCat.{2} R)).obj
    (SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X Y f).op

instance openPullback_additive : (openPullback p X Y f).Additive := by
  dsimp only [openPullback]
  infer_instance

local notation "H" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusFrameOpen.IntrinsicPadicFrobeniusFrameOpen.openPullback p X Y f

def reindex : (Framesᵒᵖ ⥤ CochainComplex (Y.left.Opensᵒᵖ ⥤ ModuleCat.{2} R) ℕ) ⥤
    (X.left.affineOpensᵒᵖ ⥤ CochainComplex (X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R) ℕ) :=
  (Functor.whiskeringLeft _ _ _).obj V ⋙
    (Functor.whiskeringRight _ _ _).obj ((H).mapHomologicalComplex (.up ℕ))

omit [X.left.IsSeparated] in
theorem open_eq : (reindex p X Y f hp).map O = FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.openTransformation p X Y f hp 0 := rfl

omit [X.left.IsSeparated] in
theorem sections_eq : (reindex p X Y f hp).map (LevelZero.FrameOpenFrobeniusNaturality.LevelZeroFrameOpenFrobeniusNaturality.sectionsMap p Y) =
    FrobeniusSectionMap.IntrinsicPadicFrobeniusSectionMap.complexes p X Y f hp :=
  Section.ComplexWhisker.SectionComplexWhisker.natural T S S P P (LevelZero.FrameFrobeniusSheaf.LevelZeroFrameFrobeniusSheaf.transformation p Y)
    (LevelZero.FrobeniusOpenMap.LevelZeroFrobeniusOpenMap.largeFunctorMap p Y) V H

omit [X.left.IsSeparated] [IsSeparated Y.hom] in
theorem source_eq : (reindex p X Y f hp).map
    (Functor.whiskerRight (LevelZero.FrameOpenFrobeniusNaturality.LevelZeroFrameOpenFrobeniusNaturality.sourceMap p Y)
      ((Functor.const Y.left.Opensᵒᵖ : ModuleCat.{2} R ⥤ Y.left.Opensᵒᵖ ⥤ ModuleCat.{2} R).mapHomologicalComplex (.up ℕ))) =
    Functor.whiskerRight (FrobeniusFrameSource.IntrinsicPadicFrobeniusFrameSource.transformation p X Y f hp)
      ((Functor.const X.left.affineOpensᵒᵖ : ModuleCat.{2} R ⥤ X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R).mapHomologicalComplex (.up ℕ)) := rfl

omit [X.left.IsSeparated] in
theorem natural : FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.openTransformation p X Y f hp 0 ≫
    FrobeniusSectionMap.IntrinsicPadicFrobeniusSectionMap.complexes p X Y f hp =
      Functor.whiskerRight (FrobeniusFrameSource.IntrinsicPadicFrobeniusFrameSource.transformation p X Y f hp)
        ((Functor.const X.left.affineOpensᵒᵖ : ModuleCat.{2} R ⥤ X.left.affineOpensᵒᵖ ⥤ ModuleCat.{2} R).mapHomologicalComplex (.up ℕ)) ≫
          FrameDiagonalMap.IntrinsicPadicFrameDiagonalMap.openTransformation p X Y f hp 0 :=
  MappedSquare.MappedSquareCoordinates.square (reindex p X Y f hp)
    O (LevelZero.FrameOpenFrobeniusNaturality.LevelZeroFrameOpenFrobeniusNaturality.sectionsMap p Y)
    (Functor.whiskerRight (LevelZero.FrameOpenFrobeniusNaturality.LevelZeroFrameOpenFrobeniusNaturality.sourceMap p Y)
      ((Functor.const Y.left.Opensᵒᵖ : ModuleCat.{2} R ⥤ Y.left.Opensᵒᵖ ⥤ ModuleCat.{2} R).mapHomologicalComplex (.up ℕ))) O
    _ _ _ _ (LevelZero.FrameOpenFrobeniusNaturality.LevelZeroFrameOpenFrobeniusNaturality.natural p Y)
    (open_eq p X Y f hp) (sections_eq p X Y f hp)
    (source_eq p X Y f hp) (open_eq p X Y f hp)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.FrobeniusFrameOpen.IntrinsicPadicFrobeniusFrameOpen
