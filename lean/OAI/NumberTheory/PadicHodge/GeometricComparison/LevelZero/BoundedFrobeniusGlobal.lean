import OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.BoundedOpenFrobenius
import OAI.NumberTheory.PadicHodge.GeometricComparison.ExactHomology
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionGlobal
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.ResolutionPresheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.InverseCoordinateHomology

/-! # Bounded Frobenius Global -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.BoundedFrobeniusGlobal.LevelZeroBoundedFrobeniusGlobal

noncomputable section

/-! Frobenius on the original injective open sections induces exactly
the original bounded crystalline Ext pullback at the top open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime] (Y : Over (Spec (CommRingCat.of (ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) 0))

local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "g" => Over.Hom.left (OAI.AlgebraicGeometry.FormalGeometry.Completion.Frobenius.Construction.finiteFieldSchemeFrobenius (ZMod p) Y)
local notation "hg" => OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.CrystallineFrobenius.LevelZeroCrystallineFrobenius.over_witt p Y
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeTopology.restriction (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) g hg 0
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.functor (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w 0
local notation "V" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex.evaluation (B := WittVector p (ZMod p)) (⊤ : Y.left.Opens)

def map := ((V).mapHomologicalComplex (.up ℕ)).map (BoundedOpenFrobenius.LevelZeroBoundedOpenFrobenius.map p Y I)

def originalMap := ((V).mapHomologicalComplex (.up ℕ)).map
  (Section.CochainPullback.SectionCochainPullback.map T S S (FrobeniusOpenMap.LevelZeroFrobeniusOpenMap.largeFunctorMap p Y)
    (IntegralComparison.BoundedGeneral.ResolutionMap.map g hg 0 I I))

theorem map_eq : LevelZeroBoundedFrobeniusGlobal.map p Y I = originalMap p Y I :=
  congrArg (fun a => ((V).mapHomologicalComplex (.up ℕ)).map
    (Section.CochainPullback.SectionCochainPullback.map T S S (FrobeniusOpenMap.LevelZeroFrobeniusOpenMap.largeFunctorMap p Y) a))
      (BoundedOpenFrobenius.LevelZeroBoundedOpenFrobenius.resolutionMap_eq p Y I)

theorem original_coordinates : (IntegralComparison.BoundedOpen.SectionGlobal.complexIso w 0 I).hom ≫ originalMap p Y I =
    IntegralComparison.BoundedGeneral.ResolutionPresheaf.map g hg 0 I I ≫
      (IntegralComparison.BoundedOpen.SectionGlobal.complexIso w 0 I).hom := by
  apply HomologicalComplex.Hom.ext
  funext i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

theorem coordinates : (IntegralComparison.BoundedOpen.SectionGlobal.complexIso w 0 I).hom ≫ LevelZeroBoundedFrobeniusGlobal.map p Y I =
    IntegralComparison.BoundedGeneral.ResolutionPresheaf.map g hg 0 I I ≫
      (IntegralComparison.BoundedOpen.SectionGlobal.complexIso w 0 I).hom :=
  (congrArg (fun a => (IntegralComparison.BoundedOpen.SectionGlobal.complexIso w 0 I).hom ≫ a) (map_eq p Y I)).trans
    (original_coordinates p Y I)

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (LevelZeroBoundedFrobeniusGlobal.map p Y I) i ≫
    (IntegralComparison.BoundedOpen.SectionGlobal.homologyIso w 0 I i).hom =
      (IntegralComparison.BoundedOpen.SectionGlobal.homologyIso w 0 I i).hom ≫
        ModuleCat.ofHom (IntegralComparison.BoundedCrystalline.CrystallinePullback.pullback g hg 0 i) := by
  have h₁ := IntegralComparison.InverseCoordinateHomology.homology
    (IntegralComparison.BoundedOpen.SectionGlobal.complexIso w 0 I) (IntegralComparison.BoundedOpen.SectionGlobal.complexIso w 0 I)
    (IntegralComparison.BoundedGeneral.ResolutionPresheaf.map g hg 0 I I) (LevelZeroBoundedFrobeniusGlobal.map p Y I)
    (coordinates p Y I).symm i
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁
    (IntegralComparison.BoundedGeneral.ResolutionPresheaf.homology g hg 0 I I i)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.LevelZero.BoundedFrobeniusGlobal.LevelZeroBoundedFrobeniusGlobal
