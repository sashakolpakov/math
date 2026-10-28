import OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.GlobalSectionPullback
import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrobeniusGlobalOpenMap
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.CochainPullback

/-! # Frame Open Frobenius -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameOpenFrobenius.LevelZeroFrameOpenFrobenius

noncomputable section

/-! The original frame-to-open-section maps commute with the actual level-zero
Frobenius restriction and its original geometric frame map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

private theorem composeSquares {D : Type*} [Category* D] {A B C E F G H K : D}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ E) (d : E ⟶ K)
    (e : B ⟶ F) (f : F ⟶ E) (g : F ⟶ G) (i : G ⟶ K) (l : A ⟶ H) (j : H ⟶ G)
    (h₁ : b ≫ c = e ≫ f) (h₂ : f ≫ d = g ≫ i) (h₃ : a ≫ e ≫ g = l ≫ j) :
    (a ≫ b) ≫ (c ≫ d) = l ≫ (j ≫ i) := by
  have h : b ≫ c ≫ d = (e ≫ g) ≫ i := by
    rw [← Category.assoc, h₁, Category.assoc, h₂, ← Category.assoc]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => a ≫ q) h).trans
      ((Category.assoc a (e ≫ g) i).symm.trans
        ((congrArg (fun q => q ≫ i) h₃).trans (Category.assoc _ _ _))))

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
variable (p : ℕ) [Fact p.Prime]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (F : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) 0)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "g" => Over.Hom.left (OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y)
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.over_witt p Y
local notation "a" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.map p Y F
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) g hg 0
local notation "Kn" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex w 0 F
local notation "Km" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex w 0 F
local notation "b" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameGeometricMap.map g hg 0 a
local notation "Sn" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 0

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

local instance constPreservesZero :
    (Functor.const Y.left.Opensᵒᵖ : ModuleCat.{2} R ⥤ Y.left.Opensᵒᵖ ⥤ ModuleCat.{2} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

def sectionsMap : ((Sn).mapHomologicalComplex (.up ℕ)).obj Km ⟶
    ((Sn).mapHomologicalComplex (.up ℕ)).obj Kn :=
  Section.CochainPullback.SectionCochainPullback.map T Sn Sn (FrobeniusOpenMap.LevelZeroFrobeniusOpenMap.largeFunctorMap p Y) b

theorem natural : (Frame.OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation w 0).app (op F) ≫
    sectionsMap p Y F =
    ((Functor.const Y.left.Opensᵒᵖ : ModuleCat.{2} R ⥤ Y.left.Opensᵒᵖ ⥤ ModuleCat.{2} R).mapHomologicalComplex (.up ℕ)).map
      (((ModuleCat.uliftFunctor.{2, 1} R).mapHomologicalComplex (.up ℕ)).map
        (IntegralComparison.BoundedFrame.SectionChange.frameMap a)) ≫
          (Frame.OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation w 0).app (op F) := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext V
  have hL := congrArg (fun q => (q.app ((Km).X i)).app V)
    (FrobeniusGlobalOpenMap.LevelZeroFrobeniusGlobalOpenMap.natural p Y)
  have hN := congrArg (fun q => q.app V)
    ((Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation w 0).naturality ((b).f i))
  have hG := congrArg (fun q => q.f i) (Frame.GlobalSectionPullback.FrameGlobalSectionPullback.natural g hg 0 a)
  change (((Frame.OpenSectionNaturality.FrameOpenSectionNaturality.globalTransformation w 0).app (op F)).f i ≫
    ((Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation w 0).app ((Km).X i)).app V) ≫
      (((FrobeniusOpenMap.LevelZeroFrobeniusOpenMap.largeFunctorMap p Y).app ((Km).X i)).app V ≫
        ((Sn).map ((b).f i)).app V) =
    ((ModuleCat.uliftFunctor.{2, 1} R).map ((IntegralComparison.BoundedFrame.SectionChange.frameMap a).f i)) ≫
      (((Frame.OpenSectionNaturality.FrameOpenSectionNaturality.globalTransformation w 0).app (op F)).f i ≫
        ((Bounded.GlobalSectionRestriction.BoundedGlobalSectionRestriction.transformation w 0).app ((Kn).X i)).app V)
  exact composeSquares _ _ _ _ _ _ _ _ _ _ hL hN.symm hG

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameOpenFrobenius.LevelZeroFrameOpenFrobenius
