/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TwistShiftIso
import OAI.AlgebraicGeometry.SheafCohomology.Projective.TensorFrameSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleCancellationPairing

/-! # Power Cancellation Pairing -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerCancellationPairing

noncomputable section

open _root_.MvPolynomial

/-! Canonical power cancellation evaluated on recursively formed local sections. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry MonoidalCategory Opposite
universe u

section

local instance cancellationPairingMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X
local instance cancellationPairingSymmetric (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Monoidal.Scheme.Modules.symmetricCategory X

theorem tensorPairing_unit_conversion {X : Scheme.{u}}
    {A B C D : X.Modules} (e : A ⊗ C ⟶ 𝟙_ X.Modules)
    (f : B ⊗ D ⟶ 𝟙_ X.Modules) :
    TensorFrameSections.tensorPairing (e ≫ (TensorSections.monoidalUnitObjIso X).hom)
        (f ≫ (TensorSections.monoidalUnitObjIso X).hom) =
      tensorμ A B C D ≫ (e ⊗ₘ f) ≫
        (λ_ (𝟙_ X.Modules)).hom ≫ (TensorSections.monoidalUnitObjIso X).hom := by
  unfold TensorFrameSections.tensorPairing TensorSections.unitObjTensorIso
  simp only [Iso.trans_hom, tensorIso_hom, Iso.symm_hom]
  simp only [tensorHom_comp_tensorHom_assoc, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

def localMonoidalUnitSection (X : Scheme.{u}) (U : X.Opens) :
    Γ(𝟙_ X.Modules, U) :=
  (TensorSections.monoidalUnitObjIso X).inv.val.app (op U) (show Γ(X, U) from 1)

theorem unitPairing_localMonoidalUnitSection (X : Scheme.{u}) (U : X.Opens) :
    ((λ_ (𝟙_ X.Modules)).hom ≫ (TensorSections.monoidalUnitObjIso X).hom).val.app (op U)
      (TensorSections.tensorSection (𝟙_ X.Modules) (𝟙_ X.Modules) U
        (localMonoidalUnitSection X U) (localMonoidalUnitSection X U)) =
      (show Γ(X, U) from 1) := by
  have he : (λ_ (𝟙_ X.Modules)).hom ≫ (TensorSections.monoidalUnitObjIso X).hom =
      ((TensorSections.monoidalUnitObjIso X).hom ⊗ₘ (TensorSections.monoidalUnitObjIso X).hom) ≫
        (TensorSections.unitObjTensorIso X).hom := by
    simp only [TensorSections.unitObjTensorIso, Iso.trans_hom, tensorIso_hom, Iso.symm_hom]
    rw [← Category.assoc, tensorHom_comp_tensorHom]
    simp only [Iso.hom_inv_id, tensorHom_id, id_whiskerRight, Category.id_comp]
  rw [he]
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
  rw [TensorFrameSections.tensorSection_map]
  have h1 : (TensorSections.monoidalUnitObjIso X).hom.val.app (op U)
      (localMonoidalUnitSection X U) = (show Γ(X, U) from 1) :=
    SectionIdentities.Scheme.Modules.iso_inv_hom_app_applyT (TensorSections.monoidalUnitObjIso X) (op U)
      (show Γ(X, U) from 1)
  rw [h1, TensorFrameSections.unitObjTensorIso_hom_tensorSection, one_mul]

end

namespace MvPolynomial
open OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerCancellationPairing
variable {R : Type u} [CommRing R] {σ : Type}
attribute [local instance] MvPolynomial.gradedAlgebra
local instance cancellationPowerMonoidal (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  Monoidal.Scheme.Modules.monoidalCategory X
local instance cancellationPowerSymmetric (X : Scheme.{u}) : SymmetricCategory X.Modules :=
  Monoidal.Scheme.Modules.symmetricCategory X

def coordinateHyperplanePowerPairing (j : σ) (n : ℕ) :
    TwistPowers.MvPolynomial.coordinateHyperplaneIdealModulePower (R := R) j n ⊗
      TwistPowers.MvPolynomial.coordinateHyperplanePoleSheafPower (R := R) j n ⟶
        Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)) :=
  (TwistShiftIso.MvPolynomial.coordinateHyperplanePowerCancellationIso (R := R) j n).hom ≫
    (TensorSections.monoidalUnitObjIso _).hom

theorem coordinateHyperplanePowerPairing_zero (j : σ) :
    coordinateHyperplanePowerPairing (R := R) j 0 =
      (λ_ (𝟙_ (Proj (homogeneousSubmodule σ R)).Modules)).hom ≫
        (TensorSections.monoidalUnitObjIso _).hom := rfl

theorem coordinateHyperplaneBaseCancellationIso_hom_pairing (j : σ) :
    (TwistShiftIso.MvPolynomial.coordinateHyperplaneBaseCancellationIso (R := R) j).hom ≫
      (TensorSections.monoidalUnitObjIso (Proj (homogeneousSubmodule σ R))).hom =
        TensorFrameSections.dualPairing (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)) := by
  simp only [TwistShiftIso.MvPolynomial.coordinateHyperplaneBaseCancellationIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    InvertibleCancellationPairing.invertibleDualPairingIso_hom]

theorem coordinateHyperplanePowerPairing_succ (j : σ) (n : ℕ) :
    coordinateHyperplanePowerPairing (R := R) j (n + 1) =
      TensorFrameSections.tensorPairing (coordinateHyperplanePowerPairing (R := R) j n)
        (TensorFrameSections.dualPairing (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))) := by
  simp only [coordinateHyperplanePowerPairing]
  rw [TwistShiftIso.MvPolynomial.coordinateHyperplanePowerCancellationIso_succ_hom,
    ← coordinateHyperplaneBaseCancellationIso_hom_pairing]
  rw [tensorPairing_unit_conversion]
  simp only [Category.assoc, HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf]

end MvPolynomial

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.PowerCancellationPairing
