import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.ConstantCochainCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.SourceComponent
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.ConeCechMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Sheaf.PresheafSectionComplex

/-! # Constant Cech Map -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.ConstantCechMap

noncomputable section

/-! The actual sheafified constant-complex section map followed by
Čech restriction equals the literal presheaf cone augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open scoped Simplicial

universe u z
variable {C : Type u} [Category.{0} C] [HasBinaryProducts C]
  {ι : Type} [Finite ι] (F : ι → C)
  (R : Type u) [CommRing R] (J : GrothendieckTopology C)
  [HasExt.{max u z} (Sheaf J (ModuleCat.{u} R))]
  (M : CochainComplex (ModuleCat.{u} R) ℕ)
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ)
  (a : ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).obj M ⟶ P)

local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.ConstantCochainCoordinates.sheafComplex R J P

def presheafComplex := ((sheafToPresheaf J (ModuleCat.{u} R)).mapHomologicalComplex (.up ℕ)).obj K

def presheafMap : ((Functor.const Cᵒᵖ).mapHomologicalComplex (.up ℕ)).obj M ⟶
    presheafComplex R J P := a ≫ CochainUnit.Pairing.unit.{u,0,u} J R P

local notation "Q" => OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.ConstantCechMap.presheafComplex R J P
local notation "D" => OAI.NumberTheory.PadicHodge.IntegralComparison.Global.SectionCechEdge.diagram R Q
local notation "s" => OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.ConstantCochainCoordinates.sectionMap R J M P a

def restriction (q : ℕ) := Cech.DiagramAugmentationCoordinates.Complex.restriction F D M
  (Presheaf.ConeCechMap.cone R M Q (presheafMap R J M P a)) q

omit [Finite ι] in
theorem restriction_square (q : ℕ) :
    (s).f q ≫ (Ext.ZeroPresheafSections.iso.{u,0,u,z} R J).hom.app ((K).X q) ≫
      (ModuleCat.uliftFunctor.{z,u} R).map
        (FrameCech.SourceComponent.restriction F R J ((K).X q)) =
    (ModuleCat.uliftFunctor.{z,u} R).map (restriction F R J M P a q) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply ULift.ext
  apply Module.ProductScalarKernel.element_ext
    (fun t : Fin 1 → ι => ((K).X q).obj.obj (op (Presentation.TupleProducts.family F 0 t)))
  intro t
  have h₁ := FrameCech.SourceComponent.restriction_apply F R J ((K).X q)
    (Ext.ZeroPresheafSections.equivalence.{u,0,u,z} R J ((K).X q)
      ((s).f q x)).down t
  have h₂ := ConcreteCategory.congr_hom
    (Pi.lift_comp_π (fun t : Fin 1 → ι =>
      ((presheafMap R J M P a).f q).app (op (Presentation.TupleProducts.family F 0 t))) t) x.down
  exact h₁.trans ((ConstantCochainCoordinates.coordinates.{u,0,z}
    R J M P a q x.down (op (Presentation.TupleProducts.family F 0 t))).trans h₂.symm)

def map := Presheaf.ConeCechMap.map R F M Q (presheafMap R J M P a)

private theorem evaluation_square {A : Type*} [Category A]
    {V W T L E : A} (a : V ⟶ W) (b : W ⟶ T) (r : T ⟶ L)
    (r' : V ⟶ L) (j : L ⟶ E) (e : T ⟶ E) (e' : V ⟶ E)
    (h : a ≫ b ≫ r = r') (he : e = r ≫ j) (he' : e' = r' ≫ j) :
    (a ≫ b) ≫ e = e' := by
  rw [he, ← Category.assoc, Category.assoc a b r, h, ← he']

theorem square : (s) ≫ (IntegralComparison.Sheaf.PresheafSectionComplex.complexIso.{u,0,u,z} R J K).hom ≫
    ((ModuleCat.uliftFunctor.{z,u} R).mapHomologicalComplex (.up ℕ)).map
      (Global.SectionCechEdge.edge R F Q) =
    ((ModuleCat.uliftFunctor.{z,u} R).mapHomologicalComplex (.up ℕ)).map
      (ConstantCechMap.map F R J M P a) := by
  apply HomologicalComplex.Hom.ext
  funext q
  have he := (congrArg (ModuleCat.uliftFunctor.{z,u} R).map
    (Global.SectionCechEdge.component R F Q q)).trans
      ((ModuleCat.uliftFunctor.{z,u} R).map_comp _ _)
  have he' := (congrArg (ModuleCat.uliftFunctor.{z,u} R).map
    (Cech.DiagramAugmentationCoordinates.Complex.augmentation_component F D M
      (Presheaf.ConeCechMap.cone R M Q (presheafMap R J M P a)) q)).trans
        ((ModuleCat.uliftFunctor.{z,u} R).map_comp _ _)
  exact (Category.assoc _ _ _).symm.trans
    (evaluation_square _ _ _ _ _ _ _ (restriction_square F R J M P a q) he he')

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Sheafified.ConstantCechMap
