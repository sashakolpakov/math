import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittCanonicalSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoefficientPresheafSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.SectionBijection
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFormDescent
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittCohomology

/-! # Witt Frame De Rham Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFrameDeRhamIso

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

variable (p : ℕ) [Fact p.Prime] (k A C σ : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra (WittVector p k) A] [Module.Flat (WittVector p k) A]
  [CommRing C] [Algebra k C] [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ (WittVector p k)) A]
  [IsScalarTower (WittVector p k) (MvPolynomial σ (WittVector p k)) A]
  [Algebra.Etale (MvPolynomial σ (WittVector p k)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ) (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k, ρ (algebraMap (WittVector p k) A w) =
    algebraMap k C (WittVector.constantCoeff w)) (n : ℕ)

local notation "W" => WittVector p k
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)

local instance structureMap_separated : IsSeparated f :=
  WittFrameProduct.structureMap_separated p k C

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothWitt.WittFrame.boundedFrame p k A C ρ hρ hker hbase n
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "τ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols.frameProjection F
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections.frameComplex f n F
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f n F
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections.sheafMap f n F

include σ in
theorem section_bijective (m : ℕ) :
    Function.Bijective (IntegralComparison.Module.ConstantSections.sectionMap R (BoundedCrystalline.Site.topology f n) ((D).X m) ((K).X m) ((a).f m)) :=
  Sheafified.SectionBijection.sectionMap_bijective R (BoundedCrystalline.Site.topology f n)
    ((Crystalline.RelativeResolution.coefficientFunctor (B := W)).obj
      (RelativeFrame.FormMap.frameModule (F).obj m))
    ((CoefficientPresheafSections.liftPresheaves W).obj
      (RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m))
    (WittFormDescent.isSheaf p k A C σ ρ hρ hker hbase n m)
    ((CoefficientPresheafSections.liftPresheaves W).map
      (RelativeFrame.FormNaturality.mapPresheaf H Q π (F).obj τ m))
    (CoefficientPresheafSections.sectionMap_bijective W
      (RelativeFrame.FormMap.frameModule (F).obj m)
      (RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m)
      (RelativeFrame.FormNaturality.mapPresheaf H Q π (F).obj τ m)
      (WittCanonicalSections.sectionMap_bijective p k A C σ ρ hρ hker hbase n m))

include σ in
theorem sectionsMap_isIso : IsIso (BoundedFrame.DeRhamSections.sectionsMap f n F) :=
  ConstantSection.ComplexIso.map_isIso R (BoundedCrystalline.Site.topology f n) D K a (section_bijective p k A C σ ρ hρ hker hbase n)

abbrev frameComplex : CochainComplex (ModuleCat.{u + 2} R) ℕ :=
  ((ModuleCat.uliftFunctor.{u + 2, u + 1} R).mapHomologicalComplex (ComplexShape.up ℕ)).obj D

def complexIso : frameComplex p k A C ρ hρ hker hbase n ≅ WittCohomology.Comparison.complex p k A C ρ hρ hker hbase n := by
  exact @asIso _ _ _ _ (BoundedFrame.DeRhamSections.sectionsMap f n F)
    (sectionsMap_isIso p k A C σ ρ hρ hker hbase n)

def homologyIso (i : ℕ) : (frameComplex p k A C ρ hρ hker hbase n).homology i ≅
    ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n i) :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso (complexIso p k A C σ ρ hρ hker hbase n) ≪≫
    WittCohomology.Comparison.homologyIso p k A C σ ρ hρ hker hbase n i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSmooth.WittFrameDeRhamIso
