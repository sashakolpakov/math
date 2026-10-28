import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalFunctorSquare
import OAI.NumberTheory.PadicHodge.IntegralComparison.ConstantSection.ComplexNaturality

/-! # Constant Ext -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantExt.ConstantExtSectionTransformation

noncomputable section

/-! A natural family of constant-sheaf complex maps induces a natural
family of the original coefficient-linear Ext-section maps. -/

open _root_.CategoryTheory

universe u v w z r s
variable {C : Type u} [Category.{v} C] (R : Type w) [CommRing R]
  (J : GrothendieckTopology C) [HasSheafify J (ModuleCat.{w} R)]
  [HasExt.{max w z} (Sheaf J (ModuleCat.{w} R))]
  {T : Type r} [Category.{s} T]
  (D : T ⥤ CochainComplex (ModuleCat.{w} R) ℕ)
  (K : T ⥤ CochainComplex (Sheaf J (ModuleCat.{w} R)) ℕ)
  (a : D ⋙ (constantSheaf J (ModuleCat.{w} R)).mapHomologicalComplex (.up ℕ) ⟶ K)

def unit : (ModuleCat.uliftFunctor.{z,w} R) ⟶ (constantSheaf J (ModuleCat.{w} R)) ⋙
    IntegralComparison.Ext.ModuleFunctor.functor R (IntegralComparison.Module.ConstantSections.constantUnit R J) 0 where
  app M := ModuleCat.ofHom ((IntegralComparison.Module.ConstantSections.globalElement R J M).comp
    ULift.moduleEquiv.toLinearMap)
  naturality M N f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (IntegralComparison.Module.ConstantSections.globalElement_natural R J f x.down).symm

def source : T ⥤ CochainComplex (ModuleCat.{max w z} R) ℕ :=
  D ⋙ (ModuleCat.uliftFunctor.{z, w} R).mapHomologicalComplex (.up ℕ)

def target : T ⥤ CochainComplex (ModuleCat.{max w z} R) ℕ :=
  K ⋙ (IntegralComparison.Ext.ModuleFunctor.functor R (IntegralComparison.Module.ConstantSections.constantUnit R J) 0).mapHomologicalComplex (.up ℕ)

def component (X : T) : (source R D).obj X ⟶ (target R J K).obj X :=
  IntegralComparison.ConstantSection.ComplexMap.map R J (D.obj X) (K.obj X) (a.app X)

theorem component_naturality (X Y : T) (f : X ⟶ Y) (i : ℕ) :
    ((source R D).map f).f i ≫ (component R J D K a Y).f i =
      (component R J D K a X).f i ≫ ((target R J K).map f).f i := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hc : (constantSheaf J (ModuleCat.{w} R)).map ((D.map f).f i) ≫ (a.app Y).f i =
      (a.app X).f i ≫ (K.map f).f i := congrArg (fun q => q.f i) (a.naturality f)
  exact (IntegralComparison.Module.ConstantSections.section_natural R J ((D.map f).f i) ((K.map f).f i)
    ((a.app X).f i) ((a.app Y).f i) hc x.down).symm

theorem naturality (X Y : T) (f : X ⟶ Y) :
    (source R D).map f ≫ component R J D K a Y =
      component R J D K a X ≫ (target R J K).map f := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact component_naturality R J D K a X Y f i

def transformation : source R D ⟶ target R J K :=
  CechCone.TotalFunctorSquare.CechConeTotalFunctorSquare.diagramMapDirect (I := T)
    (constantSheaf J (ModuleCat.{w} R)) (ModuleCat.uliftFunctor.{z,w} R)
    (IntegralComparison.Ext.ModuleFunctor.functor R (IntegralComparison.Module.ConstantSections.constantUnit R J) 0)
    D K a (unit R J)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantExt.ConstantExtSectionTransformation
