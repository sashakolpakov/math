import OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.Reduction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientMultivariableTo
import OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening

/-! # Multivariable Thickening -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableThickening.WittMultivariableThickening

noncomputable section

/-!
# Actual multivariable Witt crystalline thickenings

The multivariable divided-power rings modulo p^(n+1) have residue field
k, p is nilpotent, and their reduction kernels carry the compatible Witt
divided powers. These are actual objects of the affine crystalline site.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [hp : Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "K" => FractionRing W
local notation "I" => Ideal.span {(p : W)}
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "h" => IsFractionRing.injective W K
local notation "unit" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.base_unit p k
local notation "G" => DividedPowerAlgebra W (σ →₀ W)
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Multivariable.DividedPowers.MultivariableDividedPowers.ideal W σ I
local notation "L" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.baseIdeal p k
local notation "subDP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.baseIdeal_subDP p k

abbrev Ring (n : ℕ) := QuotientMultivariableD.QuotientMultivariableForms.Ring W σ (L n)

def quotient (n : ℕ) : G →ₐ[W] Ring p k σ n := QuotientMultivariableD.QuotientMultivariableForms.quotient W σ (L n)

def ambientReduction : G →+* k :=
  WittVector.constantCoeff.comp (Multivariable.Reduction.MultivariableReduction.augmentation W σ).toRingHom

omit [CharP k p] [PerfectRing k p] in
theorem ambientReduction_surjective : Function.Surjective (ambientReduction p k σ) := by
  intro a
  obtain ⟨w, hw⟩ := WittVector.constantCoeff_surjective p a
  refine ⟨algebraMap W G w, ?_⟩
  change WittVector.constantCoeff (Multivariable.Reduction.MultivariableReduction.augmentation W σ (algebraMap W G w)) = a
  rw [AlgHom.commutes]
  exact hw

theorem ambientReduction_kernel : RingHom.ker (ambientReduction p k σ) = IG := by
  ext a
  rw [← Multivariable.Reduction.MultivariableReduction.reduction_kernel W σ I]
  change WittVector.constantCoeff (Multivariable.Reduction.MultivariableReduction.augmentation W σ a) = 0 ↔
    Ideal.Quotient.mk I (Multivariable.Reduction.MultivariableReduction.augmentation W σ a) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change Multivariable.Reduction.MultivariableReduction.augmentation W σ a ∈ RingHom.ker WittVector.constantCoeff ↔ _
  rw [WittVector.ker_constantCoeff]

theorem quotientIdeal_le_kernel (n : ℕ) :
    (L n).map (algebraMap W G) ≤ RingHom.ker (ambientReduction p k σ) := by
  rw [ambientReduction_kernel]
  exact (QuotientMultivariableD.QuotientMultivariableForms.quotient_subDP W σ K h I δ unit (L n) (subDP n)).1

def reduction (n : ℕ) : Ring p k σ n →+* k :=
  Ideal.Quotient.lift ((L n).map (algebraMap W G)) (ambientReduction p k σ)
    (quotientIdeal_le_kernel p k σ n)

theorem reduction_quotient (n : ℕ) (a : G) :
    WittMultivariableThickening.reduction p k σ n (quotient p k σ n a) = ambientReduction p k σ a := rfl

theorem reduction_surjective (n : ℕ) : Function.Surjective (WittMultivariableThickening.reduction p k σ n) := by
  intro a
  obtain ⟨x, rfl⟩ := ambientReduction_surjective p k σ a
  exact ⟨quotient p k σ n x, rfl⟩

theorem reduction_kernel (n : ℕ) : RingHom.ker (WittMultivariableThickening.reduction p k σ n) =
    QuotientMultivariableD.QuotientMultivariableForms.ideal W σ I (L n) := by
  have hk := Ideal.ker_quotient_lift (ambientReduction p k σ) (quotientIdeal_le_kernel p k σ n)
  rw [ambientReduction_kernel] at hk
  exact hk

def kernelDividedPowers (n : ℕ) : DividedPowers (RingHom.ker (WittMultivariableThickening.reduction p k σ n)) :=
  DividedPowers.ofRingEquiv (e := RingEquiv.refl (Ring p k σ n))
    (by
      change (QuotientMultivariableD.QuotientMultivariableForms.ideal W σ I (L n)).map (RingHom.id _) = _
      rw [Ideal.map_id]
      exact (reduction_kernel p k σ n).symm)
    (QuotientMultivariableD.QuotientMultivariableForms.dividedPowers W σ K h I δ unit (L n) (subDP n))

theorem baseDP (n : ℕ) :
    DividedPowers.IsDPMorphism δ (kernelDividedPowers p k σ n) (algebraMap W (Ring p k σ n)) where
  ideal_comp := by
    rw [reduction_kernel]
    exact ((QuotientMultivariableD.QuotientMultivariableForms.quotient_isDPMorphism W σ K h I δ unit (L n) (subDP n)).comp _
      (Multivariable.DividedPowers.MultivariableDividedPowers.base_isDPMorphism W σ K h I δ unit)).ideal_comp
  dpow_comp x hx :=
    ((QuotientMultivariableD.QuotientMultivariableForms.quotient_isDPMorphism W σ K h I δ unit (L n) (subDP n)).comp _
      (Multivariable.DividedPowers.MultivariableDividedPowers.base_isDPMorphism W σ K h I δ unit)).dpow_comp x hx

omit [CharP k p] [PerfectRing k p] in
theorem p_power_zero (n : ℕ) : (p : Ring p k σ n) ^ (n + 1) = 0 := by
  have hz : quotient p k σ n (algebraMap W G ((p : W) ^ (n + 1))) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _
      (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton (p : W))) (n + 1)))
  simpa only [map_pow, map_natCast] using hz

def thickening (n : ℕ) : PD.Thickening.AffinePDThickening p k k where
  ring := CommRingCat.of (Ring p k σ n)
  reduction := WittMultivariableThickening.reduction p k σ n
  reduction_surjective := WittMultivariableThickening.reduction_surjective p k σ n
  reduction_base := by
    ext w
    change WittVector.constantCoeff (Multivariable.Reduction.MultivariableReduction.augmentation W σ (algebraMap W G w)) =
      WittVector.constantCoeff w
    rw [AlgHom.commutes]
    rfl
  p_nilpotent := ⟨n + 1, p_power_zero p k σ n⟩
  dividedPowers := kernelDividedPowers p k σ n
  baseDP := WittMultivariableThickening.baseDP p k σ n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.MultivariableThickening.WittMultivariableThickening
