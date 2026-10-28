import OAI.AlgebraicGeometry.Crystalline.Cohomology.NonemptyCechExtra
import OAI.AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi
import Mathlib.CategoryTheory.Sites.Abelian

/-! # Presentation Resolution -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution

noncomputable section

/-!
# The sheaf Čech resolution of a presentation presheaf

An objectwise nonempty presheaf of presentations has an augmented tuple
nerve. Its free-module chain complex resolves the constant rank-one
presheaf, and exact sheafification gives a resolution of the actual
constant coefficient sheaf on the site.
-/

open _root_.CategoryTheory Limits

universe u v w

variable (R : Type u) [CommRing R] {C : Type v} [Category.{w} C]
  (F : Cᵒᵖ ⥤ Type u)

def complex : ChainComplex (Cᵒᵖ ⥤ ModuleCat R) ℕ :=
  ComplexAssemblyQuasi.ComplexAssembly.complex (ComplexShape.down ℕ) (F ⋙ NonemptyCechExtra.NonemptyCechNerve.complexFunctor R)

def target : ChainComplex (Cᵒᵖ ⥤ ModuleCat R) ℕ :=
  ComplexAssemblyQuasi.ComplexAssembly.complex (ComplexShape.down ℕ) (F ⋙ NonemptyCechExtra.NonemptyCechNerve.constantFunctor R)

def rawAugmentation : complex R F ⟶ target R F :=
  ComplexAssemblyQuasi.ComplexAssembly.map (ComplexShape.down ℕ) (Functor.whiskerLeft F (NonemptyCechExtra.NonemptyCechNerve.augmentation R))

def coefficientPresheaf : Cᵒᵖ ⥤ ModuleCat R :=
  (Functor.const Cᵒᵖ).obj (ModuleCat.of R R)

def targetIso : target R F ≅
    (ChainComplex.single₀ (Cᵒᵖ ⥤ ModuleCat R)).obj (coefficientPresheaf (C := C) R) :=
  (ComplexAssemblyQuasi.ComplexAssembly.functor (ComplexShape.down ℕ)).mapIso
      (Functor.isoWhiskerLeft F (NonemptyCechExtra.NonemptyCechNerve.constantFunctorIso R)) ≪≫
    ComplexAssemblyQuasi.ComplexAssembly.constantIso (T := Cᵒᵖ) (ComplexShape.down ℕ)
      ((ChainComplex.single₀ (ModuleCat R)).obj ((ModuleCat.free R).obj PUnit)) ≪≫
    (HomologicalComplex.singleMapHomologicalComplex (Functor.const Cᵒᵖ)
      (ComplexShape.down ℕ) 0).app ((ModuleCat.free R).obj PUnit) ≪≫
    (ChainComplex.single₀ (Cᵒᵖ ⥤ ModuleCat R)).mapIso
      ((Functor.const Cᵒᵖ).mapIso (ModuleCat.FreeMonoidal.εIso R).symm)

/-- The canonical augmentation to the constant coefficient presheaf. -/
def augmentation : complex R F ⟶
    (ChainComplex.single₀ (Cᵒᵖ ⥤ ModuleCat R)).obj (coefficientPresheaf (C := C) R) :=
  rawAugmentation R F ≫ (targetIso R F).hom

instance rawAugmentation_quasiIso [∀ t, Nonempty (F.obj t)] : QuasiIso (rawAugmentation R F) :=
  ComplexAssemblyQuasi.ComplexAssembly.map_quasiIso (ComplexShape.down ℕ)
    (Functor.whiskerLeft F (NonemptyCechExtra.NonemptyCechNerve.augmentation R)) (fun t => NonemptyCechExtra.NonemptyCechNerve.augmentation_quasiIso R (F.obj t))

instance augmentation_quasiIso [∀ t, Nonempty (F.obj t)] : QuasiIso (augmentation R F) := by
  dsimp only [augmentation]
  infer_instance

variable (J : GrothendieckTopology C) [HasSheafify J (ModuleCat R)]

def sheafComplex : ChainComplex (Sheaf J (ModuleCat R)) ℕ :=
  ((presheafToSheaf J (ModuleCat R)).mapHomologicalComplex (ComplexShape.down ℕ)).obj (complex R F)

/-- The same augmentation on actual sheaves, with target the native constant sheaf. -/
def sheafAugmentation : sheafComplex R F J ⟶
    (ChainComplex.single₀ (Sheaf J (ModuleCat R))).obj
      ((constantSheaf J (ModuleCat R)).obj (ModuleCat.of R R)) :=
  ((presheafToSheaf J (ModuleCat R)).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (augmentation R F) ≫
    (HomologicalComplex.singleMapHomologicalComplex (presheafToSheaf J (ModuleCat R))
      (ComplexShape.down ℕ) 0).hom.app (coefficientPresheaf (C := C) R)

instance sheafAugmentation_quasiIso [∀ t, Nonempty (F.obj t)] :
    QuasiIso (sheafAugmentation R F J) := by
  have hmap : QuasiIso
      (((presheafToSheaf J (ModuleCat R)).mapHomologicalComplex (ComplexShape.down ℕ)).map
        (augmentation R F)) := by infer_instance
  have hiso : IsIso
      ((HomologicalComplex.singleMapHomologicalComplex (presheafToSheaf J (ModuleCat R))
        (ComplexShape.down ℕ) 0).hom.app (coefficientPresheaf (C := C) R)) := by infer_instance
  exact quasiIso_comp
    (((presheafToSheaf J (ModuleCat R)).mapHomologicalComplex (ComplexShape.down ℕ)).map
      (augmentation R F))
    ((HomologicalComplex.singleMapHomologicalComplex (presheafToSheaf J (ModuleCat R))
      (ComplexShape.down ℕ) 0).hom.app (coefficientPresheaf (C := C) R))

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.PresentationResolution.CechPresentationResolution
