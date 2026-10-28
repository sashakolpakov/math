import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveSectionCohomology

/-! # Presheaf Section Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionComplex

noncomputable section

/-!
# IntegralComparison: actual injective-resolution cohomology in presheaf-section coordinates
-/

open _root_.CategoryTheory

universe u v w z

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  [HasExt.{max u w z} (Sheaf J (ModuleCat.{w} R))]

def sectionFunctor : Sheaf J (ModuleCat.{w} R) ⥤ ModuleCat.{max u w z} R :=
  sheafToPresheaf J (ModuleCat.{w} R) ⋙
    ExhaustiveSectionNaturality.globalSectionsFunctor R (ModuleCat.of R R) ⋙
      ModuleCat.uliftFunctor.{z, max u w} R

instance sectionFunctor_additive : (sectionFunctor R J).Additive := by
  dsimp only [sectionFunctor]
  infer_instance

def complex (K : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ) :
    CochainComplex (ModuleCat.{max u w z} R) ℕ :=
  ((sectionFunctor R J).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

def complexIso (K : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ) :
    Acyclic.Resolution.Comparison.complex R (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) K ≅ complex R J K :=
  (NatIso.mapHomologicalComplex (IntegralComparison.Ext.ZeroPresheafSections.iso R J) (ComplexShape.up ℕ)).app K

def homologyIso {Z : Sheaf J (ModuleCat.{w} R)} (I : InjectiveResolution Z) (i : ℕ) :
    (complex R J I.cocomplex).homology i ≅
      ModuleCat.of R (Abelian.Ext.{max u w z} (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) Z i) :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso (complexIso R J I.cocomplex).symm ≪≫
    InjectiveSectionCohomology.homologyIso R (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) I i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionComplex
