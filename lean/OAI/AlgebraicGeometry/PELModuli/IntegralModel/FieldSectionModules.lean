import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.SchemeAbelianCohomology
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechHomologyIso
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Field Section Modules -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldSectionModules

noncomputable section

/-! Generic affine and line-bundle base change, isolated from the Openness
statement-dependent group-theoretic import chain. All constructions below
are proved here and retain the actual scheme-module section maps. -/

/-! Actual scheme-module Cech complexes over an arbitrary affine base ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

namespace FieldBaseChange

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

def baseRingConstants : R →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom

def modulesAsBaseRingSheaf : X.Modules ⥤ ArithmeticGeometry.OrdinaryLocus.Openness.ModuleSheafInjectives.Construction.ModuleSheaves R (Scheme.forgetToTop.obj X) := by
  let H := ModuleCat.restrictScalars.{u} (baseRingConstants f)
  have hH : (_root_.Opens.grothendieckTopology X).HasSheafCompose H :=
    hasSheafCompose_of_preservesLimitsOfSize (J := _root_.Opens.grothendieckTopology X) (F := H)
  exact SheafOfModules.forgetToSheafModuleCat X.ringCatSheaf (op ⊤)
    (initialOpOfTerminal isTerminalTop) ⋙
      @sheafCompose _ _ _ _ _ _ (_root_.Opens.grothendieckTopology X) H hH

def baseRingUnderlyingAbelianIso (M : X.Modules) :
    (ArithmeticGeometry.OrdinaryLocus.Openness.QuasicoherentAdditiveCech.Construction.moduleSheafToAbelian (.of R) (Scheme.forgetToTop.obj X)).obj
      ((modulesAsBaseRingSheaf f).obj M) ≅ (ArithmeticGeometry.OrdinaryLocus.Openness.SchemeAbelianCohomology.Construction.schemeModulesToAbelian X).obj M :=
  Iso.refl _

abbrev schemeModuleCechShortComplex (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    ShortComplex (ModuleCat.{u} R) :=
  ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechShortComplex.Construction.openModuleCechShortComplex ((modulesAsBaseRingSheaf f).obj M) U

def schemeModuleCechGlobalSectionsEquiv (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (hU : iSup U = ⊤) :
    ((modulesAsBaseRingSheaf f).obj M).obj.obj (op ⊤) ≃ₗ[R]
      LinearMap.ker (schemeModuleCechShortComplex f M U).f.hom :=
  ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechHomologyIso.Construction.openModuleCechGlobalSectionsEquiv ((modulesAsBaseRingSheaf f).obj M) U hU

def schemeModuleCechHomologyIso (M : X.Modules) {ι : Type u} (U : ι → X.Opens) :
    (schemeModuleCechShortComplex f M U).homology ≅
      ModuleCat.of R (ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechCohomology.Construction.OpenCechH1 ((modulesAsBaseRingSheaf f).obj M) U) :=
  ArithmeticGeometry.OrdinaryLocus.Openness.OpenCechHomologyIso.Construction.openModuleCechHomologyIso ((modulesAsBaseRingSheaf f).obj M) U

end FieldBaseChange

/-! Flatness over the base of regular functions on an affine chart of a flat scheme. -/

namespace FieldBaseChange

universe u

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))

def baseRingSectionConstants (U : X.Opens) : R →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U (by simp)).hom

def baseRingSectionsAlgebra (U : X.Opens) : CommAlgCat R :=
  letI := (baseRingSectionConstants f U).toAlgebra
  CommAlgCat.of R Γ(X, U)

def baseRingStructureSectionsIso (U : X.Opens) :
    ModuleCat.of R (baseRingSectionsAlgebra f U) ≅
      ((modulesAsBaseRingSheaf f).obj (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)).obj.obj (op U) :=
  (LinearEquiv.ofLinearMap
    { toFun := fun x ↦ x, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
    { toFun := fun x ↦ x, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
    (by ext; rfl) (by ext; rfl)).toModuleIso

theorem baseRingSectionConstants_flat [Flat f] (U : X.Opens) (hU : IsAffineOpen U) :
    (baseRingSectionConstants f U).Flat :=
  (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective).comp
    (f.flat_appLE (isAffineOpen_top _) hU (by simp))

theorem baseRingStructureSections_flat [Flat f] (U : X.Opens) (hU : IsAffineOpen U) :
    Module.Flat R (((modulesAsBaseRingSheaf f).obj (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)).obj.obj (op U)) := by
  have hflat : Module.Flat R (baseRingSectionsAlgebra f U) := baseRingSectionConstants_flat f U hU
  exact Module.Flat.of_linearEquiv (baseRingStructureSectionsIso f U).symm.toLinearEquiv

end FieldBaseChange

/-! Restriction and scheme pullback maps for regular functions as modules over an affine base ring. -/

namespace FieldBaseChange

universe u

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of R))

theorem baseRingSectionConstants_pullback (h : Y ⟶ X)
    (U : X.Opens) (V : Y.Opens) (hVU : V ≤ h ⁻¹ᵁ U) :
    (h.appLE U V hVU).hom.comp (baseRingSectionConstants f U) =
      baseRingSectionConstants (h ≫ f) V := by
  change ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U _ ≫ h.appLE U V hVU).hom = _
  exact congrArg (fun q : Γ(Spec (.of R), ⊤) ⟶ Γ(Y, V) ↦
    ((Scheme.ΓSpecIso (.of R)).inv ≫ q).hom)
    (Scheme.Hom.appLE_comp_appLE h f ⊤ U V (by simp) hVU)

def baseRingSectionsPullbackAlgHom (h : Y ⟶ X)
    (U : X.Opens) (V : Y.Opens) (hVU : V ≤ h ⁻¹ᵁ U) :
    baseRingSectionsAlgebra f U →ₐ[R] baseRingSectionsAlgebra (h ≫ f) V where
  __ := (h.appLE U V hVU).hom
  commutes' r := RingHom.congr_fun (baseRingSectionConstants_pullback f h U V hVU) r

def baseRingSectionsPullback (h : Y ⟶ X)
    (U : X.Opens) (V : Y.Opens) (hVU : V ≤ h ⁻¹ᵁ U) :
    ((modulesAsBaseRingSheaf f).obj (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)).obj.obj (op U) →ₗ[R]
      ((modulesAsBaseRingSheaf (h ≫ f)).obj (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule Y)).obj.obj (op V) :=
  (baseRingStructureSectionsIso (h ≫ f) V).toLinearEquiv.toLinearMap.comp
    ((baseRingSectionsPullbackAlgHom f h U V hVU).toLinearMap.comp
      (baseRingStructureSectionsIso f U).symm.toLinearEquiv.toLinearMap)

theorem baseRingSectionsPullback_apply (h : Y ⟶ X)
    (U : X.Opens) (V : Y.Opens) (hVU : V ≤ h ⁻¹ᵁ U)
    (x : ((modulesAsBaseRingSheaf f).obj (ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule X)).obj.obj (op U)) :
    baseRingSectionsPullback f h U V hVU x = h.appLE U V hVU x := rfl

end FieldBaseChange

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FieldSectionModules
