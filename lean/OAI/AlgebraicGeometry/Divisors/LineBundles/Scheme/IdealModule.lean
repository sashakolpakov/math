import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SchemeIdealModule
import Mathlib.Algebra.Category.ModuleCat.Kernels

/-! # Ideal Module -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealModule.BundleCycles

noncomputable section

section

/-! Sections of the actual scheme ideal module are identified with
the kernels of the genuine maps on regular functions. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

def schemeModuleEvaluation (X : Scheme.{0}) (U : X.Opens) : X.Modules ⥤ ModuleCat Γ(X, U) :=
  SheafOfModules.evaluation X.ringCatSheaf (.op U)

instance schemeModuleEvaluation_preservesFiniteLimits (X : Scheme.{0}) (U : X.Opens) :
    PreservesFiniteLimits (schemeModuleEvaluation X U) :=
  inferInstanceAs (PreservesFiniteLimits (SheafOfModules.evaluation X.ringCatSheaf (.op U)))

variable {X Z : Scheme.{0}} (f : Z ⟶ X) (U : X.Opens)

theorem schemeIdealModuleSectionKernel_eq :
    ((schemeModuleEvaluation X U).map (SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap f)).hom.ker =
      RingHom.ker (f.app U).hom := by
  ext r
  exact (congrArg (fun a => a = 0) (SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap_apply f U r)).to_iff

def schemeIdealModuleSectionsIso :
    (schemeModuleEvaluation X U).obj (SchemeIdealModule.BundleCycles.schemeIdealModule f) ≅
      ModuleCat.of Γ(X, U) (RingHom.ker (f.app U).hom) :=
  PreservesKernel.iso (schemeModuleEvaluation X U) (SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap f) ≪≫
    ModuleCat.kernelIsoKer ((schemeModuleEvaluation X U).map (SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap f)) ≪≫
    eqToIso (congrArg (fun p : Submodule Γ(X, U) Γ(X, U) => ModuleCat.of Γ(X, U) p)
      (schemeIdealModuleSectionKernel_eq f U))

end

section

/-! The sections-to-kernel isomorphism identifies the actual sheaf
inclusion with the ordinary inclusion of the function-ring ideal. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem submoduleEqIso_subtype {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    {P Q : Submodule R V} (h : P = Q) :
    (eqToIso (congrArg (fun p : Submodule R V => ModuleCat.of R p) h)).hom ≫ ModuleCat.ofHom Q.subtype =
      ModuleCat.ofHom P.subtype := by
  subst Q
  rfl

variable {X Z : Scheme.{0}} (f : Z ⟶ X) (U : X.Opens)

theorem schemeIdealModuleSectionsIso_inclusion :
    (schemeIdealModuleSectionsIso f U).hom ≫ ModuleCat.ofHom (RingHom.ker (f.app U).hom).subtype =
      (schemeModuleEvaluation X U).map (SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f) := by
  let F := schemeModuleEvaluation X U
  let φ := SchemeIdealModule.BundleCycles.schemeStructurePushforwardMap f
  let e₁ := PreservesKernel.iso F φ
  let e₂ := ModuleCat.kernelIsoKer (F.map φ)
  have h₁ := submoduleEqIso_subtype (schemeIdealModuleSectionKernel_eq f U)
  have h₂ := ModuleCat.kernelIsoKer_hom_ker_subtype (F.map φ)
  have h₃ : e₁.hom ≫ kernel.ι (F.map φ) = F.map (kernel.ι φ) := by
    rw [PreservesKernel.iso_hom]
    exact kernelComparison_comp_ι _ _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => e₁.hom ≫ k)
      ((Category.assoc _ _ _).trans ((congrArg (fun k => e₂.hom ≫ k) h₁).trans h₂))).trans h₃)

theorem schemeIdealModuleSectionsIso_apply (s : Γ(SchemeIdealModule.BundleCycles.schemeIdealModule f, U)) :
    ((schemeIdealModuleSectionsIso f U).hom s).val = (SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f).app U s := by
  have h := ConcreteCategory.congr_hom (schemeIdealModuleSectionsIso_inclusion f U)
    (s : (schemeModuleEvaluation X U).obj (SchemeIdealModule.BundleCycles.schemeIdealModule f))
  exact h

theorem schemeIdealModuleSectionsIso_inv_apply (s : RingHom.ker (f.app U).hom) :
    (SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f).app U ((schemeIdealModuleSectionsIso f U).inv s) = s.val := by
  have h := schemeIdealModuleSectionsIso_apply f U ((schemeIdealModuleSectionsIso f U).inv s)
  have he := ConcreteCategory.congr_hom (schemeIdealModuleSectionsIso f U).inv_hom_id s
  exact h.symm.trans (congrArg Subtype.val he)

end

/-! The actual ideal inclusion is linear and injective on sections,
and it commutes with restriction of regular functions. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Z : Scheme.{0}} (f : Z ⟶ X)

def schemeIdealModuleSectionLinear (U : X.Opens) : Γ(SchemeIdealModule.BundleCycles.schemeIdealModule f, U) →ₗ[Γ(X, U)] Γ(X, U) :=
  (RingHom.ker (f.app U).hom).subtype.comp (schemeIdealModuleSectionsIso f U).hom.hom

theorem schemeIdealModuleSectionLinear_apply (U : X.Opens) (s : Γ(SchemeIdealModule.BundleCycles.schemeIdealModule f, U)) :
    schemeIdealModuleSectionLinear f U s = (SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f).app U s :=
  schemeIdealModuleSectionsIso_apply f U s

theorem schemeIdealModuleSectionLinear_injective (U : X.Opens) :
    Function.Injective (schemeIdealModuleSectionLinear f U) :=
  Subtype.val_injective.comp (schemeIdealModuleSectionsIso f U).toLinearEquiv.injective

theorem schemeIdealModuleSectionLinear_mem (U : X.Opens) (s : Γ(SchemeIdealModule.BundleCycles.schemeIdealModule f, U)) :
    schemeIdealModuleSectionLinear f U s ∈ RingHom.ker (f.app U).hom :=
  ((schemeIdealModuleSectionsIso f U).hom s).property

theorem schemeIdealModuleInclusion_restrict {U V : X.Opens} (h : V ≤ U) (s : Γ(SchemeIdealModule.BundleCycles.schemeIdealModule f, U)) :
    (SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f).app V ((SchemeIdealModule.BundleCycles.schemeIdealModule f).presheaf.map (homOfLE h).op s) =
      X.presheaf.map (homOfLE h).op ((SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f).app U s) :=
  ConcreteCategory.congr_hom ((SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f).mapPresheaf.naturality (homOfLE h).op) s

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealModule.BundleCycles
