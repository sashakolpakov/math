import OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeRelativeModuleSheaf
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Cube Sections As Algebra -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeSectionsAsAlgebra.Construction.CubeCech

noncomputable section

/-! Regular functions on opens as algebras over the base field. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

def sectionConstants (U : X.Opens) : k →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom.comp (CubeProperGlobalSections.Construction.CubeCech.globalConstants f)

def sectionsAsBaseAlgebra (U : X.Opens) : CommAlgCat k :=
  letI := (sectionConstants f U).toAlgebra
  CommAlgCat.of k Γ(X, U)

def sectionsRestrictionAlgHom {U V : X.Opens} (i : V ⟶ U) :
    sectionsAsBaseAlgebra f U →ₐ[k] sectionsAsBaseAlgebra f V where
  __ := (X.presheaf.map i.op).hom
  commutes' r := by
    change X.presheaf.map i.op
      (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (CubeProperGlobalSections.Construction.CubeCech.globalConstants f r)) =
      X.presheaf.map (homOfLE le_top : V ⟶ ⊤).op (CubeProperGlobalSections.Construction.CubeCech.globalConstants f r)
    rw [← ConcreteCategory.comp_apply, ← X.presheaf.map_comp]
    rfl

def sectionsAsBaseModuleIso (U : X.Opens) :
    ModuleCat.of k (sectionsAsBaseAlgebra f U) ≅
      (CubeRelativeModuleSheaf.Construction.CubeCech.structureSheafAsBaseFieldSheaf f).obj.obj (op U) :=
  (LinearEquiv.ofLinearMap
    { toFun := fun x ↦ x, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
    { toFun := fun x ↦ x, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
    (by ext; rfl) (by ext; rfl)).toModuleIso

theorem sectionConstants_eq_appLE (U : X.Opens) :
    sectionConstants f U = ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom := by
  rfl

theorem sectionConstants_pullback {Y : Scheme.{u}} (h : Y ⟶ X)
    (U : X.Opens) (V : Y.Opens) (hVU : V ≤ h ⁻¹ᵁ U) :
    (h.appLE U V hVU).hom.comp (sectionConstants f U) = sectionConstants (h ≫ f) V := by
  rw [sectionConstants_eq_appLE, sectionConstants_eq_appLE, ← CommRingCat.hom_comp,
    Category.assoc]
  exact congrArg (fun q : Γ(Spec (.of k), ⊤) ⟶ Γ(Y, V) ↦
    ((Scheme.ΓSpecIso (.of k)).inv ≫ q).hom)
    (Scheme.Hom.appLE_comp_appLE h f ⊤ U V (by simp) hVU)

def sectionsPullbackAlgHom {Y : Scheme.{u}} (h : Y ⟶ X)
    (U : X.Opens) (V : Y.Opens) (hVU : V ≤ h ⁻¹ᵁ U) :
    sectionsAsBaseAlgebra f U →ₐ[k] sectionsAsBaseAlgebra (h ≫ f) V where
  __ := (h.appLE U V hVU).hom
  commutes' r := RingHom.congr_fun (sectionConstants_pullback f h U V hVU) r

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.CubeSectionsAsAlgebra.Construction.CubeCech
