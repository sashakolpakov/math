import OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialMk
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialReduction
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Thickening
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation

/-! # Thickening -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening

noncomputable section

/-!
# The finite-level Witt divided-polynomial crystalline objects

The rings used in the quotient Poincaré lemma are actual crystalline
thickenings of the residue field. Their reduction kernel carries the
constructed divided powers, compatible with the canonical Witt powers.
-/

open _root_.CategoryTheory

universe u

variable (p : ℕ) [hp : Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]

local notation "W" => WittVector p k
local notation "K" => FractionRing W
local notation "I" => Ideal.span {(p : W)}
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "h" => IsFractionRing.injective W K
local notation "G" => DividedPowerAlgebra W W
local notation "IG" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers.ideal W I

omit [PerfectRing k p] in
theorem base_unit : ∃ a ∈ I, IsUnit (algebraMap W K a) := by
  refine ⟨p, Ideal.subset_span (Set.mem_singleton _), isUnit_iff_ne_zero.mpr ?_⟩
  rw [map_natCast]
  exact Nat.cast_ne_zero.mpr hp.out.ne_zero

local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Divided.PolynomialPowers.DividedPolynomialPowers.dividedPowers W K h I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.base_unit p k)

def baseIdeal (n : ℕ) : Ideal W := I ^ (n + 1)

omit [PerfectRing k p] in
theorem baseIdeal_subDP (n : ℕ) : DividedPowers.IsSubDPIdeal δ (baseIdeal p k n) :=
  PD.Truncation.PDTruncation.power_isSubDPIdeal W I δ n

abbrev Ring (n : ℕ) := QuotientPolynomialEq.QuotientPolynomialForms.Ring W (baseIdeal p k n)

def quotient (n : ℕ) : G →ₐ[W] Ring p k n := QuotientPolynomialEq.QuotientPolynomialForms.quotient W (baseIdeal p k n)

def ambientReduction : G →+* k :=
  WittVector.constantCoeff.comp (Divided.PolynomialReduction.DividedPolynomialReduction.augmentation W).toRingHom

omit [CharP k p] [PerfectRing k p] in
theorem ambientReduction_surjective : Function.Surjective (ambientReduction p k) := by
  intro a
  obtain ⟨w, hw⟩ := WittVector.constantCoeff_surjective p a
  refine ⟨algebraMap W G w, ?_⟩
  change WittVector.constantCoeff (Divided.PolynomialReduction.DividedPolynomialReduction.augmentation W (algebraMap W G w)) = a
  rw [AlgHom.commutes]
  exact hw

theorem ambientReduction_kernel : RingHom.ker (ambientReduction p k) = IG := by
  ext a
  rw [← Divided.PolynomialReduction.DividedPolynomialReduction.reduction_kernel W I]
  change WittVector.constantCoeff (Divided.PolynomialReduction.DividedPolynomialReduction.augmentation W a) = 0 ↔
    Ideal.Quotient.mk I (Divided.PolynomialReduction.DividedPolynomialReduction.augmentation W a) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change Divided.PolynomialReduction.DividedPolynomialReduction.augmentation W a ∈ RingHom.ker WittVector.constantCoeff ↔ _
  rw [WittVector.ker_constantCoeff]

theorem quotientIdeal_le_kernel (n : ℕ) :
    (baseIdeal p k n).map (algebraMap W G) ≤ RingHom.ker (ambientReduction p k) := by
  rw [ambientReduction_kernel]
  exact (QuotientPolynomialEq.QuotientPolynomialForms.quotient_subDP W K h I δ (base_unit p k)
    (baseIdeal p k n) (baseIdeal_subDP p k n)).1

def reduction (n : ℕ) : Ring p k n →+* k :=
  Ideal.Quotient.lift ((baseIdeal p k n).map (algebraMap W G)) (ambientReduction p k)
    (quotientIdeal_le_kernel p k n)

@[simp] theorem reduction_quotient (n : ℕ) (a : G) :
    WittPolynomialThickening.reduction p k n (quotient p k n a) = ambientReduction p k a := rfl

theorem reduction_surjective (n : ℕ) : Function.Surjective (WittPolynomialThickening.reduction p k n) := by
  intro a
  obtain ⟨x, rfl⟩ := ambientReduction_surjective p k a
  exact ⟨quotient p k n x, rfl⟩

theorem reduction_kernel (n : ℕ) : RingHom.ker (WittPolynomialThickening.reduction p k n) =
    QuotientPolynomialEq.QuotientPolynomialForms.ideal W I (baseIdeal p k n) := by
  have hk := Ideal.ker_quotient_lift (ambientReduction p k) (quotientIdeal_le_kernel p k n)
  rw [ambientReduction_kernel] at hk
  exact hk

local notation "ε" => fun n => OAI.AlgebraicGeometry.Crystalline.Cohomology.QuotientPolynomialEq.QuotientPolynomialForms.dividedPowers W K h I δ (OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening.base_unit p k)
  (baseIdeal p k n) (baseIdeal_subDP p k n)

def kernelDividedPowers (n : ℕ) : DividedPowers (RingHom.ker (WittPolynomialThickening.reduction p k n)) :=
  DividedPowers.ofRingEquiv (e := RingEquiv.refl (Ring p k n))
    (by
      change (QuotientPolynomialEq.QuotientPolynomialForms.ideal W I (baseIdeal p k n)).map (RingHom.id _) = _
      rw [Ideal.map_id]
      exact (reduction_kernel p k n).symm) (ε n)

theorem baseDP (n : ℕ) :
    DividedPowers.IsDPMorphism δ (kernelDividedPowers p k n) (algebraMap W (Ring p k n)) where
  ideal_comp := by
    rw [reduction_kernel]
    exact ((QuotientPolynomialEq.QuotientPolynomialForms.quotient_isDPMorphism W K h I δ (base_unit p k)
      (baseIdeal p k n) (baseIdeal_subDP p k n)).comp _
        (Divided.PolynomialPowers.DividedPolynomialPowers.base_isDPMorphism W K h I δ (base_unit p k))).ideal_comp
  dpow_comp x hx :=
    ((QuotientPolynomialEq.QuotientPolynomialForms.quotient_isDPMorphism W K h I δ (base_unit p k)
      (baseIdeal p k n) (baseIdeal_subDP p k n)).comp _
        (Divided.PolynomialPowers.DividedPolynomialPowers.base_isDPMorphism W K h I δ (base_unit p k))).dpow_comp x hx

omit [CharP k p] [PerfectRing k p] in
theorem p_power_zero (n : ℕ) : (p : Ring p k n) ^ (n + 1) = 0 := by
  have hz : quotient p k n (algebraMap W G ((p : W) ^ (n + 1))) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _
      (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton (p : W))) (n + 1)))
  simpa only [map_pow, map_natCast] using hz

/-- The actual crystalline thickening with ambient ring Γ(W)/p^(n+1). -/
def thickening (n : ℕ) : PD.Thickening.AffinePDThickening p k k where
  ring := CommRingCat.of (Ring p k n)
  reduction := WittPolynomialThickening.reduction p k n
  reduction_surjective := WittPolynomialThickening.reduction_surjective p k n
  reduction_base := by
    ext w
    change ambientReduction p k (algebraMap W G w) = WittVector.constantCoeff w
    change WittVector.constantCoeff (Divided.PolynomialReduction.DividedPolynomialReduction.augmentation W (algebraMap W G w)) = _
    rw [AlgHom.commutes]
    rfl
  p_nilpotent := ⟨n + 1, p_power_zero p k n⟩
  dividedPowers := kernelDividedPowers p k n
  baseDP := WittPolynomialThickening.baseDP p k n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.Thickening.WittPolynomialThickening
