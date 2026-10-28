import OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.PrincipalSections
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.SliceStructure
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Modules -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Modules

noncomputable section

/-!
# IntegralComparison: the actual crystalline coefficients on the affine Zariski basis

The natural ring identifications respect the original base-ring action.
They identify crystalline coefficients with the restriction of the
quasicoherent structure module of the ambient affine scheme.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Localization
open OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalOpens.Category (Principal toOpens)
open OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Functor OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.PrincipalSections

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} (U : BigCrystallineSite.Object p B J δ f)

abbrev modulePresheaf : (PrincipalOpens.Category.Principal U.ring)ᵒᵖ ⥤ ModuleCat.{u} B :=
  (CrystallinePrincipal.Functor.inclusion U).op ⋙ (Over.forget U).op ⋙ BigCrystallineCohomology.modulePresheaf f

abbrev affineModulePresheaf : (PrincipalOpens.Category.Principal U.ring)ᵒᵖ ⥤ ModuleCat.{u} B :=
  (PrincipalOpens.Category.toOpens U.ring).op ⋙ structurePresheafInModuleCat U.ring U.ring ⋙
    ModuleCat.restrictScalars U.base

def moduleSectionsHom (r : PrincipalOpens.Category.Principal U.ring) :
    (modulePresheaf U).obj (op r) ⟶ (affineModulePresheaf U).obj (op r) := by
  letI := (unop ((Over.forget U).op.obj ((CrystallinePrincipal.Functor.inclusion U).op.obj (op r)))).base.toAlgebra
  letI : Module B ((structurePresheafInModuleCat U.ring U.ring).obj
      ((PrincipalOpens.Category.toOpens U.ring).op.obj (op r))) := Module.compHom _ U.base
  refine ModuleCat.ofHom
    { toFun := fun x => (PrincipalSections.sectionsEquiv U r) x
      map_add' := fun x y => (PrincipalSections.sectionsEquiv U r).map_add x y
      map_smul' := ?_ }
  intro b x
  change Crystalline.Localization.Ring U r.function at x
  change (PrincipalSections.sectionsEquiv U r) (algebraMap U.ring (Crystalline.Localization.Ring U r.function) (U.base b) * x) =
    (U.base b) • (PrincipalSections.sectionsEquiv U r) x
  rw [map_mul, (PrincipalSections.sectionsEquiv U r).commutes, Algebra.smul_def]

theorem moduleSectionsHom_apply (r : PrincipalOpens.Category.Principal U.ring) (x : (modulePresheaf U).obj (op r)) :
    moduleSectionsHom U r x = PrincipalSections.sectionsEquiv U r x := rfl

theorem modulePresheaf_map_apply {r s : PrincipalOpens.Category.Principal U.ring} (a : r ⟶ s)
    (x : (modulePresheaf U).obj (op s)) :
    (modulePresheaf U).map a.op x = ((CrystallinePrincipal.Functor.inclusion U).map a).left.ringMap x := rfl

theorem affineModulePresheaf_map_apply {r s : PrincipalOpens.Category.Principal U.ring} (a : r ⟶ s)
    (x : (affineModulePresheaf U).obj (op s)) :
    (affineModulePresheaf U).map a.op x = (PrincipalSections.zariskiPresheaf U).map a.op x := rfl

theorem moduleSectionsHom_natural_apply {r s : PrincipalOpens.Category.Principal U.ring} (a : r ⟶ s)
    (x : (modulePresheaf U).obj (op s)) :
    moduleSectionsHom U r ((modulePresheaf U).map a.op x) =
      (affineModulePresheaf U).map a.op (moduleSectionsHom U s x) := by
  erw [moduleSectionsHom_apply U r, moduleSectionsHom_apply U s,
    modulePresheaf_map_apply U a, affineModulePresheaf_map_apply U a]
  exact PrincipalSections.sections_natural_apply U a x

theorem moduleSectionsHom_natural {r s : PrincipalOpens.Category.Principal U.ring} (a : r ⟶ s) :
    (modulePresheaf U).map a.op ≫ moduleSectionsHom U r =
      moduleSectionsHom U s ≫ (affineModulePresheaf U).map a.op :=
  ModuleCat.hom_ext (LinearMap.ext (moduleSectionsHom_natural_apply U a))

def moduleSectionsIso (r : PrincipalOpens.Category.Principal U.ring) :
    (modulePresheaf U).obj (op r) ≅ (affineModulePresheaf U).obj (op r) := by
  have : IsIso (moduleSectionsHom U r) :=
    (ConcreteCategory.isIso_iff_bijective (moduleSectionsHom U r)).mpr (PrincipalSections.sectionsEquiv U r).bijective
  exact asIso (moduleSectionsHom U r)

theorem moduleSectionsIso_hom_apply (r : PrincipalOpens.Category.Principal U.ring) (x : (modulePresheaf U).obj (op r)) :
    (moduleSectionsIso U r).hom x = PrincipalSections.sectionsEquiv U r x := rfl

theorem moduleSections_natural {r s : PrincipalOpens.Category.Principal U.ring} (a : r ⟶ s) :
    (modulePresheaf U).map a.op ≫ (moduleSectionsIso U r).hom =
      (moduleSectionsIso U s).hom ≫ (affineModulePresheaf U).map a.op :=
  moduleSectionsHom_natural U a

def modulePresheafIso : modulePresheaf U ≅ affineModulePresheaf U :=
  NatIso.ofComponents (fun r => moduleSectionsIso U r.unop) (fun a => moduleSections_natural U a.unop)

def zariskiUnitPresheaf : (PrincipalOpens.Category.Principal U.ring)ᵒᵖ ⥤ ModuleCat.{u} B :=
  (PrincipalOpens.Category.toOpens U.ring).op ⋙ (modulesSpecToSheaf.obj (tilde (ModuleCat.of U.ring U.ring))).obj ⋙
    ModuleCat.restrictScalars U.base

def unitPresheafIso : modulePresheaf U ≅ zariskiUnitPresheaf U :=
  modulePresheafIso U ≪≫ Functor.isoWhiskerLeft (PrincipalOpens.Category.toOpens U.ring).op
    (Functor.isoWhiskerRight (tilde.modulesSpecToSheafIso (ModuleCat.of U.ring U.ring)).symm
      (ModuleCat.restrictScalars U.base))

abbrev Coeff := Extension.Coeff (B := B)

abbrev coefficientLift : ModuleCat.{u} B ⥤ ModuleCat.{u + 1} (Coeff (B := B)) :=
  ModuleCat.uliftFunctor.{u + 1} B ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : Coeff (B := B) ≃+* B).toRingHom

def zariskiLargePresheaf : (PrincipalOpens.Category.Principal U.ring)ᵒᵖ ⥤ ModuleCat.{u + 1} (Coeff (B := B)) :=
  zariskiUnitPresheaf U ⋙ coefficientLift

def coefficientAssociation : Crystalline.SliceStructure.principalPresheaf U ≅
    modulePresheaf U ⋙ coefficientLift :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; rfl)

/-- The identification includes the exact coefficient universe lift of IntegralComparison. -/
def largeUnitPresheafIso : Crystalline.SliceStructure.principalPresheaf U ≅ zariskiLargePresheaf U :=
  coefficientAssociation U ≪≫ Functor.isoWhiskerRight (unitPresheafIso U) coefficientLift

theorem zariskiLargePresheaf_isSheaf : Presheaf.IsSheaf (Principal.Topology.topology U.ring)
    (zariskiLargePresheaf U) :=
  (Presheaf.isSheaf_of_iso_iff (largeUnitPresheafIso U)).mp
    (Crystalline.SliceStructure.principalPresheaf_isSheaf U)

def zariskiUnitSheaf : Extension.PrincipalSheaf U :=
  ⟨zariskiLargePresheaf U, zariskiLargePresheaf_isSheaf U⟩

def coefficientSheafIso : Crystalline.SliceStructure.principalStructureSheaf U ≅ zariskiUnitSheaf U :=
  ObjectProperty.isoMk _ (largeUnitPresheafIso U)

/-- Actual crystalline slice cohomology with its native affine Zariski coefficients. -/
def cohomologyEquiv (n : ℕ) : Crystalline.SliceStructure.Cohomology U n ≃ₗ[Coeff (B := B)]
    Abelian.Ext.{u + 2} (Constant.Comparison.principalConstantUnit U) (zariskiUnitSheaf U) n :=
  (Crystalline.SliceStructure.cohomologyEquiv U n).trans
    (Etale.Frobenius.extIsoCongr (Coeff (B := B)) (Iso.refl _) (coefficientSheafIso U) n)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CrystallinePrincipal.Modules
