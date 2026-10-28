import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Support
import OAI.NumberTheory.PadicHodge.IntegralComparison.PropertySections

/-! # Section Global -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionGlobal

noncomputable section

/-!
# IntegralComparison: global sections of the open-section complex compute the original bounded crystalline Ext
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)

def linearEquiv (F : BoundedCrystalline.Site.ModuleSheaf (p := p) (J := J) (δ := δ) fY n) :
    ((Functor.const (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n)ᵒᵖ).obj
      (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B))) ⟶ F.obj) ≃ₗ[Crystalline.ExactRestriction.Coeff (B := B)]
      ((SectionPresheaf.functor fY n).obj F).obj (op ⊤) :=
  PropertySections.linearEquiv (Crystalline.ExactRestriction.Coeff (B := B)) (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B)))
    (SectionPresheaf.property fY n ⊤) (Support.property_top fY n) F.obj

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
  (p := p) (J := J) (δ := δ) fY n))

def globalComplex : CochainComplex (ModuleCat.{u + 2} (Crystalline.ExactRestriction.Coeff (B := B))) ℕ :=
  Sheaf.PresheafSectionComplex.complex.{u + 1, u, u + 1, u + 2} (Crystalline.ExactRestriction.Coeff (B := B))
    (BoundedCrystalline.Site.topology fY n) I.cocomplex

def complexIso : globalComplex fY n I ≅
    ((SectionComplex.evaluation (B := B) (⊤ : Y.Opens)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (SectionComplex.complex fY n I) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => (ModuleCat.uliftFunctor.{u + 2, u + 1} (Crystalline.ExactRestriction.Coeff (B := B))).mapIso
      (linearEquiv fY n (I.cocomplex.X i)).toModuleIso)
    (by
      intro i j hij
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

def homologyIso (i : ℕ) :
    (((SectionComplex.evaluation (B := B) (⊤ : Y.Opens)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (SectionComplex.complex fY n I)).homology i ≅
      ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B))
        (BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) fY n i) :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso (complexIso fY n I).symm ≪≫
    Sheaf.PresheafSectionComplex.homologyIso.{u + 1, u, u + 1, u + 2}
      (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology fY n) I i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionGlobal
