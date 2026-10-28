/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
This file has been modified.
-/
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Evaluation
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Invertible

/-! # Invertible Evaluation -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleEvaluation

noncomputable section

open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.SheafOfModules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open _root_.CategoryTheory MonoidalCategory

namespace SheafOfModules

open Opposite

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u})

theorem evalSection_unit_mul (U : C) [∀ V, IsMulCommutative (R.obj.obj V)]
    (φ : (_root_.SheafOfModules.unit R).over U ⟶
      _root_.SheafOfModules.unit (R.over U))
    (r : (_root_.SheafOfModules.unit R).val.obj (op U)) :
    Evaluation.SheafOfModules.evalSection R (_root_.SheafOfModules.unit R) U φ r =
      Evaluation.SheafOfModules.evalSection R (_root_.SheafOfModules.unit R) U φ
        (show (_root_.SheafOfModules.unit R).val.obj (op U) from (1 : R.obj.obj (op U))) *
        (show R.obj.obj (op U) from r) := by
  have h := Evaluation.SheafOfModules.evalSection_smul_right R (_root_.SheafOfModules.unit R) U φ
    (show R.obj.obj (op U) from r)
    (show (_root_.SheafOfModules.unit R).val.obj (op U) from (1 : R.obj.obj (op U)))
  rw [show ((show R.obj.obj (op U) from r) •
      (show (_root_.SheafOfModules.unit R).val.obj (op U) from (1 : R.obj.obj (op U))) :
        (_root_.SheafOfModules.unit R).val.obj (op U)) = r from by
    show (show R.obj.obj (op U) from r) * (1 : R.obj.obj (op U)) = r
    rw [mul_one]] at h
  rw [h, smul_eq_mul]
  exact mul_comm' _ _

theorem evalSection_unit_one (U : C)
    (φ : (_root_.SheafOfModules.unit R).over U ⟶
      _root_.SheafOfModules.unit (R.over U)) :
    Evaluation.SheafOfModules.evalSection R (_root_.SheafOfModules.unit R) U φ
        (show (_root_.SheafOfModules.unit R).val.obj (op U) from (1 : R.obj.obj (op U))) =
      φ.val.app (op (Over.mk (𝟙 U)))
        (show (R.over U).obj.obj (op (Over.mk (𝟙 U))) from 1) := by
  simp only [Evaluation.SheafOfModules.evalSection_eq]
  congr 1
  show R.obj.map (𝟙 U).op (1 : R.obj.obj (op U)) = (1 : R.obj.obj (op U))
  rw [op_id, R.obj.map_id]
  rfl

/-- **Factorization of the evaluation through a trivialization**: for an isomorphism
`ψ: M|ᵤ ≅ 𝒪|ᵤ` on the over-site, every functional is a scalar multiple of `ψ.hom`, and
the evaluation factors accordingly. -/
theorem evalSection_factor (M : _root_.SheafOfModules R) (U : C)
    [∀ V, IsMulCommutative (R.obj.obj V)]
    (ψ : M.over U ≅ _root_.SheafOfModules.unit (R.over U))
    (φ : M.over U ⟶ _root_.SheafOfModules.unit (R.over U)) (m : M.val.obj (op U)) :
    Evaluation.SheafOfModules.evalSection R M U φ m =
      Dual.SheafOfModules.dualUnitSectionsEquiv R U (ψ.inv ≫ φ) * Evaluation.SheafOfModules.evalSection R M U ψ.hom m := by
  have hφ : φ = ψ.hom ≫ (ψ.inv ≫ φ) := by rw [Iso.hom_inv_id_assoc]
  have hε : (ψ.inv ≫ φ) = Dual.SheafOfModules.overUnitScalarEnd R U (Dual.SheafOfModules.dualUnitSectionsEquiv R U (ψ.inv ≫ φ)) :=
    ((Dual.SheafOfModules.dualUnitSectionsEquiv R U).symm_apply_apply (ψ.inv ≫ φ)).symm
  calc Evaluation.SheafOfModules.evalSection R M U φ m
      = Evaluation.SheafOfModules.evalSection R M U (ψ.hom ≫ Dual.SheafOfModules.overUnitScalarEnd R U
          (Dual.SheafOfModules.dualUnitSectionsEquiv R U (ψ.inv ≫ φ))) m := by rw [← hε, ← hφ]
    _ = Evaluation.SheafOfModules.evalSection R M U (letI := Dual.SheafOfModules.dualSectionsModule R M U
          Dual.SheafOfModules.dualUnitSectionsEquiv R U (ψ.inv ≫ φ) • ψ.hom) m := rfl
    _ = Dual.SheafOfModules.dualUnitSectionsEquiv R U (ψ.inv ≫ φ) • Evaluation.SheafOfModules.evalSection R M U ψ.hom m :=
        Evaluation.SheafOfModules.evalSection_smul_left R M U ψ.hom _ m
    _ = Dual.SheafOfModules.dualUnitSectionsEquiv R U (ψ.inv ≫ φ) * Evaluation.SheafOfModules.evalSection R M U ψ.hom m := rfl

/-- Evaluation against (the hom of) a trivialization is bijective: it is the composite of
the section equivalences with the bijective sections-map of an isomorphism. -/
theorem bijective_evalSection_iso (M : _root_.SheafOfModules R) (U : C)
    (ψ : M.over U ≅ _root_.SheafOfModules.unit (R.over U)) :
    Function.Bijective (fun m => Evaluation.SheafOfModules.evalSection R M U ψ.hom m) := by
  have hcomp : (fun m => Evaluation.SheafOfModules.evalSection R M U ψ.hom m) =
      (Dual.SheafOfModules.overUnitSectionEquiv R U).symm ∘
        (fun s => _root_.SheafOfModules.sectionsMap ψ.hom s) ∘
        (Evaluation.SheafOfModules.overSectionEquiv R M U) := rfl
  rw [hcomp]
  refine Function.Bijective.comp (Equiv.bijective _)
    (Function.Bijective.comp ?_ (Equiv.bijective _))
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun s => _root_.SheafOfModules.sectionsMap ψ.inv s, fun s => ?_, fun s => ?_⟩
  · show _root_.SheafOfModules.sectionsMap ψ.inv
      (_root_.SheafOfModules.sectionsMap ψ.hom s) = s
    rw [← _root_.SheafOfModules.sectionsMap_comp, Iso.hom_inv_id,
      _root_.SheafOfModules.sectionsMap_id]
  · show _root_.SheafOfModules.sectionsMap ψ.hom
      (_root_.SheafOfModules.sectionsMap ψ.inv s) = s
    rw [← _root_.SheafOfModules.sectionsMap_comp, Iso.inv_hom_id,
      _root_.SheafOfModules.sectionsMap_id]

end SheafOfModules

namespace Scheme.Modules
variable {X : Scheme.{u}}
local instance (X : Scheme.{u}) :
    ∀ U, IsMulCommutative (X.ringCatSheaf.obj.obj U) := fun U => by
  change IsMulCommutative (X.presheaf.obj U)
  exact IsMulCommutative.of_comm fun a b => mul_comm a b

/-- **[PAIR-4′]** On an open where `M` trivializes, the component of the presheaf
evaluation is bijective: conjugate the pairing by the trivialization and its induced
dual-trivialization; the conjugated pairing is the unit multiplication (the component
content of `isIso_ev_unitObj`). Section-level — no functor conjugation. -/
theorem bijective_evPre_app_of_triv {M : X.Modules} {W : X.Opens}
    (e : (Modules.pullback W.ι).obj M ≅ Invertible.Scheme.Modules.unitObj W.toScheme) :
    Function.Bijective ((Evaluation.Scheme.Modules.evPre M).app (Opposite.op W)) := by
  let := Dual.SheafOfModules.dualSectionsModule X.ringCatSheaf M W
  -- the over-trivialization and the packaged bijective evaluation against it
  let ψ : M.over W ≅ SheafOfModules.unit (X.ringCatSheaf.over W) :=
    Invertible.Scheme.Modules.overTrivializationOfRestrictIso M W ((restrictFunctorIsoPullback W.ι).app M ≪≫ e)
  let hL : M.val.obj (Opposite.op W) ≃ₗ[X.ringCatSheaf.obj.obj (Opposite.op W)]
      X.ringCatSheaf.obj.obj (Opposite.op W) :=
    LinearEquiv.ofBijective
      { toFun := fun m => Evaluation.SheafOfModules.evalSection X.ringCatSheaf M W ψ.hom m
        map_add' := fun a b =>
          Evaluation.SheafOfModules.evalSection_add_right X.ringCatSheaf M W ψ.hom a b
        map_smul' := fun c a =>
          Evaluation.SheafOfModules.evalSection_smul_right X.ringCatSheaf M W ψ.hom c a }
      (InvertibleEvaluation.SheafOfModules.bijective_evalSection_iso X.ringCatSheaf M W ψ)
  let : CommSemiring ↑(X.ringCatSheaf.obj.obj (Opposite.op W)) :=
    inferInstanceAs (CommSemiring ↑(X.sheaf.obj.obj (Opposite.op W)))
  let : Module ↑(X.ringCatSheaf.obj.obj (Opposite.op W))
      ↑(M.val.obj (Opposite.op W)) :=
    inferInstanceAs (Module ↑(X.sheaf.obj.obj (Opposite.op W))
      ↑(M.val.obj (Opposite.op W)))
  let : Module ↑(X.ringCatSheaf.obj.obj (Opposite.op W))
      ↑((Dual.Scheme.Modules.dualObj M).val.obj (Opposite.op W)) :=
    inferInstanceAs (Module ↑(X.sheaf.obj.obj (Opposite.op W))
      ↑((Dual.Scheme.Modules.dualObj M).val.obj (Opposite.op W)))
  let : Module ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).obj (Opposite.op W))
      (TensorProduct (X.sheaf.obj.obj (Opposite.op W))
        (PresheafOfModulesOfCommRing.obj M.val (Opposite.op W))
        (PresheafOfModulesOfCommRing.obj (Dual.Scheme.Modules.dualObj M).val (Opposite.op W))) :=
    inferInstanceAs (Module (X.sheaf.obj.obj (Opposite.op W))
      (TensorProduct (X.sheaf.obj.obj (Opposite.op W))
        (PresheafOfModulesOfCommRing.obj M.val (Opposite.op W))
        (PresheafOfModulesOfCommRing.obj (Dual.Scheme.Modules.dualObj M).val (Opposite.op W))))
  -- the inverse component `c ↦ hL⁻¹ c ⊗ ψ.hom`, as a hom of module categories
  let k : (𝟙_ (_root_.PresheafOfModules
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat))).obj (Opposite.op W) ⟶
      (M.val ⊗ (Dual.Scheme.Modules.dualObj M).val : _root_.PresheafOfModules
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat)).obj (Opposite.op W) :=
    ModuleCat.ofHom
      (((TensorProduct.mk (X.ringCatSheaf.obj.obj (Opposite.op W))
        (M.val.obj (Opposite.op W)) ((Dual.Scheme.Modules.dualObj M).val.obj (Opposite.op W))).flip ψ.hom) ∘ₗ
        hL.symm.toLinearMap)
  have hki : k ≫ (Evaluation.Scheme.Modules.evPre M).app (Opposite.op W) = 𝟙 _ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun c => ?_)
    simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply]
    exact hL.apply_symm_apply c
  have hik : (Evaluation.Scheme.Modules.evPre M).app (Opposite.op W) ≫ k = 𝟙 _ := by
    refine ModuleCat.MonoidalCategory.tensor_ext fun m φ => ?_
    have hc := InvertibleEvaluation.SheafOfModules.evalSection_factor X.ringCatSheaf M W ψ φ m
    -- the inverse image of the evaluation is the scalar times the section
    have hsm : hL.symm (Evaluation.SheafOfModules.evalSection X.ringCatSheaf M W φ m) =
        Dual.SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf W (ψ.inv ≫ φ) • m :=
      hL.injective ((hL.apply_symm_apply _).trans (hc.trans
        ((_root_.map_smul hL _ m).trans (smul_eq_mul _ _)).symm))
    -- the scalar times the trivialization is the functional
    have hcψ : Dual.SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf W
        (ψ.inv ≫ φ) • ψ.hom = φ := by
      show ψ.hom ≫ Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf W
        (Dual.SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf W (ψ.inv ≫ φ)) = φ
      exact (congrArg (fun t => ψ.hom ≫ t)
        ((Dual.SheafOfModules.dualUnitSectionsEquiv
          X.ringCatSheaf W).symm_apply_apply (ψ.inv ≫ φ))).trans (Iso.hom_inv_id_assoc ψ φ)
    exact (congrArg (fun x => x ⊗ₜ[X.ringCatSheaf.obj.obj (Opposite.op W)] ψ.hom) hsm).trans
      ((TensorProduct.smul_tmul _ m ψ.hom).trans (congrArg (fun y => m ⊗ₜ y) hcψ))
  have : IsIso ((Evaluation.Scheme.Modules.evPre M).app (Opposite.op W)) := ⟨k, hik, hki⟩
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

/-- **[CMP-PAIR]** For an invertible module the evaluation pairing against the sheaf dual
(consumed from `Picard/Dual.lean`) is an isomorphism onto the unit: the presheaf pairing
is bijective on every open inside the trivializing cover
(`bijective_evPre_app_of_triv` after `restrictTrivialization`), hence locally bijective,
hence inverted by the sheafification. -/
theorem isIso_eval_of_isInvertible {M : X.Modules} (hM : Invertible.Scheme.Modules.IsInvertible M) :
    IsIso (Evaluation.Scheme.Modules.ev M) := by
  obtain ⟨ι, U, hU, htriv⟩ := hM
  have hw : OfModulesMonoidal.PresheafOfModules.sheafificationW (𝟙 X.ringCatSheaf.obj) (Evaluation.Scheme.Modules.evPre M) := by
    refine Invertible.Scheme.Modules.sheafificationW_of_bijective_on_cover (Evaluation.Scheme.Modules.evPre M) U hU (fun i W hW => ?_)
    obtain ⟨e⟩ := htriv i
    exact bijective_evPre_app_of_triv (Invertible.Scheme.Modules.restrictTrivialization hW e)
  rw [OfModulesMonoidal.PresheafOfModules.sheafificationW_iff] at hw
  have : IsIso ((PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map (Evaluation.Scheme.Modules.evPre M)) := hw
  have : IsIso (Evaluation.Scheme.Modules.ev M) := by
    let eSheaf := asIso ((PresheafOfModules.sheafification
      (𝟙 X.ringCatSheaf.obj)).map (Evaluation.Scheme.Modules.evPre M))
    let eFinal := eSheaf ≪≫ Invertible.Scheme.Modules.sheafifyValIso (Invertible.Scheme.Modules.unitObj X)
    change IsIso eFinal.hom
    exact eFinal.isIso_hom
  infer_instance

noncomputable def invertibleEvaluationIso {M : X.Modules} (hM : Invertible.Scheme.Modules.IsInvertible M) :
    Invertible.Scheme.Modules.tensorObj M (Dual.Scheme.Modules.dualObj M) ≅ Invertible.Scheme.Modules.unitObj X := by
  letI : IsIso (Evaluation.Scheme.Modules.ev M) := isIso_eval_of_isInvertible hM
  exact asIso (Evaluation.Scheme.Modules.ev M)

end Scheme.Modules

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleEvaluation
