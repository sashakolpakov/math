import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.LocalizationUniversal
import OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizationReductionKernel
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Thickening

/-! # Localized PD -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizedPD.LocalizedPDThickening

noncomputable section

/-!
# Principal-open localization of actual PD thickenings

The ambient ring and residue ring are localized at a coefficient and its
residue. The actual reduction remains surjective with the localized kernel.
The constructed localized divided powers preserve Witt-base compatibility
and nilpotence of p, giving another actual crystalline thickening.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [Fact p.Prime] (k A : Type u) [Field k] [CharP k p]
  [CommRing A] [Algebra k A] (T : PD.Thickening.AffinePDThickening p k A) (s : T.ring)

local notation "W" => WittVector p k
local notation "R" => T.ring
local notation "RS" => Localization.Away s
local notation "AS" => Localization.Away (T.reduction s)
local notation "I" => RingHom.ker T.reduction
local notation "J" => Ideal.map (algebraMap R RS) I
local notation "r" => OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizationReductionKernel.LocalizationReduction.map R A T.reduction s
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Localization.PDLocalization.dividedPowers R RS (Submonoid.powers s) I T.dividedPowers

def dividedPowers : DividedPowers (RingHom.ker r) :=
  DividedPowers.ofRingEquiv (e := RingEquiv.refl RS)
    (by
      change (J).map (RingHom.id RS) = _
      rw [Ideal.map_id, LocalizationReductionKernel.LocalizationReduction.kernel]) γ

theorem identity_isDPMorphism :
    DividedPowers.IsDPMorphism γ (LocalizedPDThickening.dividedPowers p k A T s) (RingHom.id RS) where
  ideal_comp := by rw [Ideal.map_id, LocalizationReductionKernel.LocalizationReduction.kernel]
  dpow_comp _ _ := rfl

theorem identity_inverse_isDPMorphism :
    DividedPowers.IsDPMorphism (LocalizedPDThickening.dividedPowers p k A T s) γ (RingHom.id RS) where
  ideal_comp := by rw [Ideal.map_id, LocalizationReductionKernel.LocalizationReduction.kernel]
  dpow_comp _ _ := rfl

theorem coefficients_isDPMorphism :
    DividedPowers.IsDPMorphism T.dividedPowers (LocalizedPDThickening.dividedPowers p k A T s) (algebraMap R RS) :=
  (identity_isDPMorphism p k A T s).comp _
    (PD.Localization.PDLocalization.base_isDPMorphism R RS (Submonoid.powers s) I T.dividedPowers)

def thickening : PD.Thickening.AffinePDThickening p k AS where
  ring := CommRingCat.of RS
  reduction := r
  reduction_surjective := LocalizationReductionKernel.LocalizationReduction.surjective R A T.reduction s T.reduction_surjective
  reduction_base := by
    ext w
    change r (algebraMap W RS w) = algebraMap k AS (WittVector.constantCoeff w)
    rw [IsScalarTower.algebraMap_apply W R RS, LocalizationReductionKernel.LocalizationReduction.map_algebraMap]
    have hb := DFunLike.congr_fun T.reduction_base w
    change T.reduction (algebraMap W R w) = algebraMap k A (WittVector.constantCoeff w) at hb
    rw [hb, IsScalarTower.algebraMap_apply k A AS]
  p_nilpotent := by
    have hp := T.p_nilpotent.map (algebraMap R RS)
    simpa only [map_natCast] using hp
  dividedPowers := LocalizedPDThickening.dividedPowers p k A T s
  baseDP := by
    have hd := (coefficients_isDPMorphism p k A T s).comp _ T.baseDP
    rw [← IsScalarTower.algebraMap_eq W R RS] at hd
    exact hd

def ambientMap : R →ₐ[W] RS := IsScalarTower.toAlgHom W R RS

def reducedMap : A →ₐ[k] AS := IsScalarTower.toAlgHom k A AS

theorem reduction_comm (x : R) :
    (thickening p k A T s).reduction (ambientMap p k A T s x) =
      reducedMap p k A T s (T.reduction x) :=
  LocalizationReductionKernel.LocalizationReduction.map_algebraMap R A T.reduction s x

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.LocalizedPD.LocalizedPDThickening
