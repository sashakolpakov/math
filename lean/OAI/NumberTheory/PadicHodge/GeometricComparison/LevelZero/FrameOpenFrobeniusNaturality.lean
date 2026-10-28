import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameOpenFrobeniusCombined
import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrobeniusFrameComplex
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexBifunctorChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameFrobeniusSheaf
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjective

/-! # Frame Open Frobenius Naturality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameOpenFrobeniusNaturality.LevelZeroFrameOpenFrobeniusNaturality

noncomputable section

/-! Actual Frobenius commutes naturally with frame-to-open-section
comparison on the full crystalline frame category. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
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
local notation "G" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.coefficients p
local notation "A" => OAI.NumberTheory.PadicHodge.GeometricComparison.Frame.OpenSectionNaturality.FrameOpenSectionNaturality.source (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 0

local instance separated : IsSeparated w := by
  dsimp only [IntegralComparison.Witt.Crystalline.wittStructureMap]
  infer_instance

local instance constPreservesZero :
    (Functor.const Y.left.Opensᵒᵖ : ModuleCat.{2} R ⥤ Y.left.Opensᵒᵖ ⥤ ModuleCat.{2} R).PreservesZeroMorphisms where
  map_zero _ _ := rfl

def sourceMap : A ⟶ A :=
  Functor.whiskerRight (FrobeniusFrameComplex.LevelZeroFrobeniusFrameComplex.transformation p Y) ((G).mapHomologicalComplex (.up ℕ))

def sectionsMap : P ⋙ (S).mapHomologicalComplex (.up ℕ) ⟶ P ⋙ (S).mapHomologicalComplex (.up ℕ) :=
  Section.ComplexBifunctorChange.SectionComplexBifunctorChange.complexes T S S P P (FrameFrobeniusSheaf.LevelZeroFrameFrobeniusSheaf.transformation p Y)
    (FrobeniusOpenMap.LevelZeroFrobeniusOpenMap.largeFunctorMap p Y)

omit [IsSeparated Y.hom] in
theorem source_component (F : IntegralComparison.BoundedCrystalline.Site.Objects (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) 0) :
    (sourceMap p Y).app (op F) = ((ModuleCat.uliftFunctor.{2, 1} R).mapHomologicalComplex (.up ℕ)).map
      (IntegralComparison.BoundedFrame.SectionChange.frameMap (CrystallineFrobenius.LevelZeroCrystallineFrobenius.map p Y F)) := by
  change ((G).mapHomologicalComplex (.up ℕ)).map
    ((FrobeniusFrameComplex.LevelZeroFrobeniusFrameComplex.pulled p Y).app (op F) ≫ 𝟙 _) = _
  rw [Category.comp_id]
  rfl

theorem natural : Frame.OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation w 0 ≫ sectionsMap p Y =
    Functor.whiskerRight (sourceMap p Y)
      ((Functor.const Y.left.Opensᵒᵖ : ModuleCat.{2} R ⥤ Y.left.Opensᵒᵖ ⥤ ModuleCat.{2} R).mapHomologicalComplex (.up ℕ)) ≫
        Frame.OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation w 0 := by
  apply NatTrans.ext
  funext F
  apply HomologicalComplex.Hom.ext
  funext i
  apply NatTrans.ext
  funext V
  have h := FrameOpenFrobeniusCombined.LevelZeroFrameOpenFrobeniusCombined.natural p Y F.unop
  have hc := source_component p Y F.unop
  exact (congrArg (fun q => (q.f i).app V) h).trans
    (congrArg (fun a => a ≫ (((Frame.OpenSectionNaturality.FrameOpenSectionNaturality.openTransformation w 0).app F).f i).app V)
      (congrArg (fun q => q.f i) hc).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.FrameOpenFrobeniusNaturality.LevelZeroFrameOpenFrobeniusNaturality
