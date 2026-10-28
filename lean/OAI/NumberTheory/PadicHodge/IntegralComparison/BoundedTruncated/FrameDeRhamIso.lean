import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.CanonicalSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.CoefficientPresheafSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.SectionBijection
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexIso
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FormDescent
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.Cohomology

/-! # Frame De Rham Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FrameDeRhamIso

noncomputable section

/-!
# IntegralComparison: the original bounded affine crystalline cohomology is frame de Rham cohomology

The isomorphism is induced by the canonical map from the original
Witt-relative frame complex, with the actual differentials and coefficient
actions. The target is the previously defined bounded crystalline Ext.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [Fintype k] [CharP k p]
  (n : ℕ) (A C σ : Type) [CommRing A] [CommRing C]
  [Algebra (Truncated.Witt.Ring p k n) A]
  [Algebra.Smooth (Truncated.Witt.Ring p k n) A] [Algebra k C]
  [LinearOrder σ] [Fintype σ]
  [Algebra (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  [IsScalarTower (Truncated.Witt.Ring p k n)
    (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  [Algebra.Etale (MvPolynomial σ (Truncated.Witt.Ring p k n)) A]
  (ρ : A →+* C) (hρ : Function.Surjective ρ)
  (hker : RingHom.ker ρ = Ideal.span {(p : A)})
  (hbase : ∀ w : WittVector p k,
    ρ (algebraMap (Truncated.Witt.Ring p k n) A (Truncated.Witt.quotient p k n w)) =
      algebraMap k C (WittVector.constantCoeff w))

local notation "W" => WittVector p k
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := W)
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k (OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Presentation.affineScheme k C)

local instance structureMap_separated : IsSeparated f :=
  FrameProduct.structureMap_separated p k C

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.SmoothFrame.boundedFrame p A C ρ hρ hker k n hbase
local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := Ideal.span {(p : W)})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram F
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection F
local notation "τ" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Symbols.frameProjection F
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections.frameComplex f n F
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f n F
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.DeRhamSections.sheafMap f n F

include σ in
omit [Fintype k] in
theorem section_bijective (m : ℕ) :
    Function.Bijective (Module.ConstantSections.sectionMap R (BoundedCrystalline.Site.topology f n) ((D).X m) ((K).X m) ((a).f m)) :=
  Sheafified.SectionBijection.sectionMap_bijective R (BoundedCrystalline.Site.topology f n)
    ((Crystalline.RelativeResolution.coefficientFunctor (B := W)).obj
      (RelativeFrame.FormMap.frameModule (F).obj m))
    ((CoefficientPresheafSections.liftPresheaves W).obj
      (RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m))
    (FormDescent.isSheaf p k n A C σ ρ hρ hker hbase m)
    ((CoefficientPresheafSections.liftPresheaves W).map
      (RelativeFrame.FormNaturality.mapPresheaf H Q π (F).obj τ m))
    (CoefficientPresheafSections.sectionMap_bijective W
      (RelativeFrame.FormMap.frameModule (F).obj m)
      (RelativeCrystalline.ModuleMaps.formsPresheaf H Q π m)
      (RelativeFrame.FormNaturality.mapPresheaf H Q π (F).obj τ m)
      (CanonicalSections.sectionMap_bijective p k n A C σ ρ hρ hker hbase m))

include σ in
omit [Fintype k] in
theorem sectionsMap_isIso : IsIso (BoundedFrame.DeRhamSections.sectionsMap f n F) :=
  ConstantSection.ComplexIso.map_isIso R (BoundedCrystalline.Site.topology f n) D K a (section_bijective p k n A C σ ρ hρ hker hbase)

abbrev frameComplex : CochainComplex (ModuleCat.{2} R) ℕ :=
  ((ModuleCat.uliftFunctor.{2, 1} R).mapHomologicalComplex (ComplexShape.up ℕ)).obj D

def complexIso : frameComplex p k n A C ρ hρ hker hbase ≅ Cohomology.Comparison.complex p k n A C ρ hρ hker hbase := by
  exact @asIso _ _ _ _ (BoundedFrame.DeRhamSections.sectionsMap f n F)
    (sectionsMap_isIso p k n A C σ ρ hρ hker hbase)

def homologyIso (i : ℕ) : (frameComplex p k n A C ρ hρ hker hbase).homology i ≅
    ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : W)}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k) f n i) :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso (complexIso p k n A C σ ρ hρ hker hbase) ≪≫
    Cohomology.Comparison.homologyIso p k n A C σ ρ hρ hker hbase i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedTruncated.FrameDeRhamIso
