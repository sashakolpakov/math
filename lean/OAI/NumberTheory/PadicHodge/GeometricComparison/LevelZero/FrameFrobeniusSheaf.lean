import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius
import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackSheafNaturality
import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.ResolutionFunctor

/-! # Frame Frobenius Sheaf -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameFrobeniusSheaf.LevelZeroFrameFrobeniusSheaf

noncomputable section

/-! Level-zero Frobenius acts on the full functor of original frame
sheaf complexes, naturally in the frame and preserving its augmentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
variable (p : ℕ) [Fact p.Prime] (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "g" => Over.Hom.left (OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y)
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.over_witt p Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) g hg 0

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

def transformation : BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 0 ⋙
      (R).mapHomologicalComplex (.up ℕ) ⟶
    BoundedFrame.ResolutionFunctor.BoundedFrameResolutionFunctor.sheafFunctor w 0 where
  app U := BoundedFrame.PullbackSheaf.BoundedFramePullbackSheaf.map g hg 0 U.unop U.unop (CrystallineFrobenius.LevelZeroCrystallineFrobenius.map p Y U.unop)
  naturality := by
    intro U V a
    exact BoundedFrame.PullbackSheafNaturality.BoundedFramePullbackSheafNaturality.natural g hg 0 a.unop a.unop
      (CrystallineFrobenius.LevelZeroCrystallineFrobenius.map p Y V.unop) (CrystallineFrobenius.LevelZeroCrystallineFrobenius.map p Y U.unop)
      ((CrystallineFrobenius.LevelZeroCrystallineFrobenius.transformation p Y).naturality a.unop)

theorem augmentation (U : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) 0) :
    IntegralComparison.BoundedFrame.PullbackAugmentation.augmentation g hg 0 U ≫ (transformation p Y).app (op U) =
      IntegralComparison.Bounded.RelativeSheafComplex.augmentation w 0 U :=
  BoundedFrame.PullbackSheaf.BoundedFramePullbackSheaf.augmentation g hg 0 U U (CrystallineFrobenius.LevelZeroCrystallineFrobenius.map p Y U)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameFrobeniusSheaf.LevelZeroFrameFrobeniusSheaf
