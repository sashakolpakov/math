import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroCanonicalSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoefficientPresheafSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.SectionBijection
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFormDescent
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroCohomology

/-! # Zero Frame De Rham Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFrameDeRhamIso

noncomputable section

/-!
# IntegralComparison: the original bounded affine crystalline cohomology is frame de Rham cohomology

The isomorphism is induced by the canonical map from the original
Witt-relative frame complex, with the actual differentials and coefficient
actions. The target is the previously defined bounded crystalline Ext.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

universe u

variable (p : ℕ) [Fact p.Prime] (k C σ : Type u) [Field k] [Fintype k] [CharP k p]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ k) C] [IsScalarTower k (MvPolynomial σ k) C]
  [Algebra.Etale (MvPolynomial σ k) C]

local notation "W" => WittVector p k
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.LevelFrame.boundedFrame p k C
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "τ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols.frameProjection F
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections.frameComplex f 0 F
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f 0 F
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections.sheafMap f 0 F

include σ in
theorem section_bijective (m : ℕ) :
    Function.Bijective (Module.ConstantSections.sectionMap R (BoundedCrystalline.Site.topology f 0) ((D).X m) ((K).X m) ((a).f m)) :=
  Sheafified.SectionBijection.sectionMap_bijective R (BoundedCrystalline.Site.topology f 0)
    ((Crystalline.RelativeResolution.coefficientFunctor (B := W)).obj
      (RelativeFrame.FormMap.frameModule (F).obj m))
    ((CoefficientPresheafSections.liftPresheaves W).obj
      (RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m))
    (ZeroFormDescent.isSheaf p k C σ m)
    ((CoefficientPresheafSections.liftPresheaves W).map
      (RelativeFrame.FormNaturality.mapPresheaf H Q π (F).obj τ m))
    (CoefficientPresheafSections.sectionMap_bijective W
      (RelativeFrame.FormMap.frameModule (F).obj m)
      (RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m)
      (RelativeFrame.FormNaturality.mapPresheaf H Q π (F).obj τ m)
      (ZeroCanonicalSections.sectionMap_bijective p k C σ m))

include σ in
theorem sectionsMap_isIso : IsIso (BoundedFrame.DeRhamSections.sectionsMap f 0 F) :=
  ConstantSection.ComplexIso.map_isIso R (BoundedCrystalline.Site.topology f 0) D K a (section_bijective p k C σ)

abbrev frameComplex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (ComplexShape.up ℕ)).obj D

def complexIso : frameComplex p k C ≅ ZeroCohomology.Comparison.complex p k C := by
  exact @asIso _ _ _ _ (BoundedFrame.DeRhamSections.sectionsMap f 0 F)
    (sectionsMap_isIso p k C σ)

def homologyIso (i : ℕ) : (frameComplex p k C).homology i ≅
    ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f 0 i) :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso (complexIso p k C σ) ≪≫
    ZeroCohomology.Comparison.homologyIso p k C σ i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedEtale.ZeroFrameDeRhamIso
