/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.AffineRankOne
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-! # Ideal Module -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.IdealModule

noncomputable section

/-! The genuine kernel ideal module and its affine sections. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open _root_.CategoryTheory Limits _root_.AlgebraicGeometry Opposite
universe u

local instance idealEvaluationAdditive (Y : Scheme.{u}) (U : Y.Opens) :
    (SheafOfModules.evaluation Y.ringCatSheaf (op U)).Additive := by
  dsimp only [SheafOfModules.evaluation]
  infer_instance

/-- Multiplication by a nonzerodivisor identifies a ring with the principal ideal it
generates. Unlike `LinearEquiv.toSpanNonzeroSingleton`, this does not require the
ambient ring to be a domain. -/
noncomputable def principalIdealEquiv {R : Type*} [CommRing R]
    (r : R) (hr : r ∈ nonZeroDivisors R) :
    R ≃ₗ[R] (Ideal.span {r} : Ideal R) :=
  (LinearEquiv.ofInjective (LinearMap.toSpanSingleton R R r)
      (by
        rw [← LinearMap.ker_eq_bot]
        exact LinearMap.ker_toSpanSingleton_eq_bot_iff.mpr
          (mem_nonZeroDivisors_iff_right.mp hr))).trans
    (LinearEquiv.ofEq _ _ (LinearMap.range_toSpanSingleton r))

@[simp]
theorem principalIdealEquiv_apply {R : Type*} [CommRing R]
    (r : R) (hr : r ∈ nonZeroDivisors R) (a : R) :
    principalIdealEquiv r hr a =
      (⟨a * r, Ideal.mul_mem_left _ a (Ideal.mem_span_singleton_self r)⟩ :
        Ideal.span {r}) :=
  rfl

private theorem ofEq_coe {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] (P Q : Submodule R M) (h : P = Q) (x : P) :
    (((LinearEquiv.ofEq P Q h) x : Q) : M) = x := by
  subst Q
  rfl

/-- The raw sheaf-of-modules kernel defining the ideal of a morphism. -/
noncomputable def idealModuleRaw {X Y : Scheme.{u}} (f : X ⟶ Y) :
    SheafOfModules Y.ringCatSheaf :=
  kernel (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)

/-- The ideal module of a morphism: the kernel of
`O_Y -> f_* O_X` in the abelian category of sheaves of `O_Y`-modules. -/
noncomputable def idealModule {X Y : Scheme.{u}} (f : X ⟶ Y) : Y.Modules :=
  idealModuleRaw f

/-- The ideal module is canonically a submodule of the structure sheaf. -/
noncomputable def idealModuleToUnit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    idealModule f ⟶ Invertible.Scheme.Modules.unitObj Y :=
  kernel.ι (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)

/-- On an affine open, `idealModule f` is the module attached to the affine ideal
recorded by `f.ker`. -/
noncomputable def idealModuleAppIdealIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (U : Y.affineOpens) :
    (SheafOfModules.evaluation Y.ringCatSheaf (.op U.1)).obj (idealModule f) ≅
      ModuleCat.of Γ(Y, U.1) (f.ker.ideal U) := by
  refine (PreservesKernel.iso (SheafOfModules.evaluation Y.ringCatSheaf (.op U.1))
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)).trans
    ((ModuleCat.kernelIsoKer _).trans ?_)
  exact (LinearEquiv.ofEq _ _ (by rw [Scheme.Hom.ker_apply]; rfl)).toModuleIso

/-- The affine ideal comparison respects its inclusion in the structure sheaf. -/
theorem idealModuleAppIdealIso_comp_subtype {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (U : Y.affineOpens) :
    (idealModuleAppIdealIso f U).hom ≫ ModuleCat.ofHom (f.ker.ideal U).subtype =
      (SheafOfModules.evaluation Y.ringCatSheaf (op U.1)).map (idealModuleToUnit f) := by
  let F : Y.Modules ⥤ ModuleCat Γ(Y, U.1) :=
    SheafOfModules.evaluation Y.ringCatSheaf (op U.1)
  have : F.PreservesZeroMorphisms :=
    inferInstanceAs (SheafOfModules.evaluation Y.ringCatSheaf (op U.1)).PreservesZeroMorphisms
  have : PreservesLimits F :=
    inferInstanceAs (PreservesLimits (SheafOfModules.evaluation Y.ringCatSheaf (op U.1)))
  let g := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have hker : (F.map g).hom.ker = f.ker.ideal U := by
    rw [Scheme.Hom.ker_apply]
    rfl
  have heq : (LinearEquiv.ofEq (R := Γ(Y, U.1)) _ _ hker).toModuleIso.hom ≫
      ModuleCat.ofHom (f.ker.ideal U).subtype =
      ModuleCat.ofHom (F.map g).hom.ker.subtype := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ofEq_coe _ _ hker x
  change ((PreservesKernel.iso F g).hom ≫
      (ModuleCat.kernelIsoKer (F.map g)).hom ≫
      (LinearEquiv.ofEq _ _ hker).toModuleIso.hom) ≫ _ = F.map (kernel.ι g)
  rw [Category.assoc, Category.assoc, heq]
  rw [ModuleCat.kernelIsoKer_hom_ker_subtype]
  rw [PreservesKernel.iso_hom, kernelComparison_comp_ι]

@[simp]
theorem idealModuleAppIdealIso_coe {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] (U : Y.affineOpens) (x : Γ(idealModule f, U.1)) :
    ((idealModuleAppIdealIso f U).hom x : Γ(Y, U.1)) =
      (idealModuleToUnit f).val.app (op U.1) x := by
  have h := ConcreteCategory.congr_hom (idealModuleAppIdealIso_comp_subtype f U) x
  exact h

/-- The kernel ideal of an affine morphism is quasicoherent. -/
theorem idealModule_quasicoherent {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] : (idealModule f).IsQuasicoherent := by
  have : (Invertible.Scheme.Modules.unitObj X).IsQuasicoherent :=
    InvertibleFinitePresentation.invertible_quasicoherent Invertible.Scheme.Modules.isInvertible_unit
  have : (Invertible.Scheme.Modules.unitObj Y).IsQuasicoherent :=
    InvertibleFinitePresentation.invertible_quasicoherent Invertible.Scheme.Modules.isInvertible_unit
  have : ((Scheme.Modules.pushforward f).obj
      (Invertible.Scheme.Modules.unitObj X)).IsQuasicoherent :=
    Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f
  exact Quasicoherent.Scheme.Modules.isQuasicoherent_kernel
    (M := Invertible.Scheme.Modules.unitObj Y)
    (N := (Scheme.Modules.pushforward f).obj (Invertible.Scheme.Modules.unitObj X))
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.IdealModule
