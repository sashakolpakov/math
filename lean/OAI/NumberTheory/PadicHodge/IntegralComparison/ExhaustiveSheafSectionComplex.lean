import OAI.NumberTheory.PadicHodge.IntegralComparison.Ext.ZeroPresheafSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.InjectiveSectionCohomology

/-! # Exhaustive Sheaf Section Complex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveSheafSectionComplex

noncomputable section

/-!
# IntegralComparison: original sheaf cohomology from compatible bounded resolution sections
-/

open _root_.CategoryTheory

universe u v w z

variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  [HasExt.{max u w z} (Sheaf J (ModuleCat.{w} R))]
  (P : ℕ → ObjectProperty C) (hP : Monotone P) (hC : ∀ U, ∃ n, P n U)

def boundedFunctor : Sheaf J (ModuleCat.{w} R) ⥤ ModuleCat.{max u w z} R :=
  sheafToPresheaf J (ModuleCat.{w} R) ⋙
    ExhaustiveSectionNaturality.boundedSectionsFunctor R P hP (ModuleCat.of R R) ⋙
      ModuleCat.uliftFunctor.{z, max u w} R

instance boundedFunctor_additive : (boundedFunctor R J P hP).Additive := by
  dsimp only [boundedFunctor]
  infer_instance

def functorIso : IntegralComparison.Ext.ModuleFunctor.functor R (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) 0 ≅
    boundedFunctor R J P hP :=
  IntegralComparison.Ext.ZeroPresheafSections.iso R J ≪≫ Functor.isoWhiskerLeft (sheafToPresheaf J (ModuleCat.{w} R))
    (Functor.isoWhiskerRight (ExhaustiveSectionNaturality.iso R P hP hC (ModuleCat.of R R))
      (ModuleCat.uliftFunctor.{z, max u w} R))

def complex (K : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ) :
    CochainComplex (ModuleCat.{max u w z} R) ℕ :=
  ((boundedFunctor R J P hP).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

def complexIso (K : CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ) :
    Acyclic.Resolution.Comparison.complex R (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) K ≅
      complex R J P hP K :=
  (NatIso.mapHomologicalComplex (functorIso R J P hP hC) (ComplexShape.up ℕ)).app K

def homologyIso {Z : Sheaf J (ModuleCat.{w} R)} (I : InjectiveResolution Z) (i : ℕ) :
    (complex R J P hP I.cocomplex).homology i ≅
      ModuleCat.of R (Abelian.Ext.{max u w z} (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) Z i) :=
  (HomologicalComplex.homologyFunctor _ _ i).mapIso (complexIso R J P hP hC I.cocomplex).symm ≪≫
    InjectiveSectionCohomology.homologyIso R (IntegralComparison.Ext.ZeroPresheafSections.constantUnit R J) I i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ExhaustiveSheafSectionComplex
