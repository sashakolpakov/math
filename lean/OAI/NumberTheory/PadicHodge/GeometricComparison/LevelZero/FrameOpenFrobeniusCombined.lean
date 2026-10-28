import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameOpenFrobenius
import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackCoordinates

/-! # Frame Open Frobenius Combined -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameOpenFrobeniusCombined.LevelZeroFrameOpenFrobeniusCombined

noncomputable section

/-! The original open-section Frobenius square also holds for the
natural combined frame-map construction used by the full Cech resolution. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (F : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) 0)

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "g" => Over.Hom.left (OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y)
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.over_witt p Y
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) g hg 0
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 0
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex w 0 F

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

local instance constPreservesZero :
    (Functor.const Y.left.Opensᵒᵖ : ModuleCat.{2} R ⥤ Y.left.Opensᵒᵖ ⥤ ModuleCat.{2} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

def map : ((S).mapHomologicalComplex (.up ℕ)).obj K ⟶ ((S).mapHomologicalComplex (.up ℕ)).obj K :=
  Section.CochainPullback.SectionCochainPullback.map T S S (FrobeniusOpenMap.LevelZeroFrobeniusOpenMap.largeFunctorMap p Y)
    (BoundedFrame.PullbackSheaf.BoundedFramePullbackSheaf.map g hg 0 F F (CrystallineFrobenius.LevelZeroCrystallineFrobenius.map p Y F))

theorem map_eq : LevelZeroFrameOpenFrobeniusCombined.map p Y F = FrameOpenFrobenius.LevelZeroFrameOpenFrobenius.sectionsMap p Y F :=
  congrArg (Section.CochainPullback.SectionCochainPullback.map T S S (FrobeniusOpenMap.LevelZeroFrobeniusOpenMap.largeFunctorMap p Y))
    (BoundedFrame.PullbackCoordinates.BoundedFramePullbackCoordinates.map_eq g hg 0 F (CrystallineFrobenius.LevelZeroCrystallineFrobenius.map p Y F))

theorem natural : (Frame.OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation w 0).app (op F) ≫ LevelZeroFrameOpenFrobeniusCombined.map p Y F =
    ((Functor.const Y.left.Opensᵒᵖ : ModuleCat.{2} R ⥤ Y.left.Opensᵒᵖ ⥤ ModuleCat.{2} R).mapHomologicalComplex (.up ℕ)).map
      (((ModuleCat.uliftFunctor.{2, 1} R).mapHomologicalComplex (.up ℕ)).map
        (IntegralComparison.BoundedFrame.SectionChange.frameMap (CrystallineFrobenius.LevelZeroCrystallineFrobenius.map p Y F))) ≫
          (Frame.OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation w 0).app (op F) :=
  (congrArg (fun a => (Frame.OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation w 0).app (op F) ≫ a) (map_eq p Y F)).trans
    (FrameOpenFrobenius.LevelZeroFrameOpenFrobenius.natural p Y F)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameOpenFrobeniusCombined.LevelZeroFrameOpenFrobeniusCombined
