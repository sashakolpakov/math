import OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineTwistCohomology
import OAI.NumberTheory.PadicHodge.PeriodInvariants.WittFrobeniusGeometry
import OAI.NumberTheory.PadicHodge.PeriodInvariants.SemilinearBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.Global.Crystalline

/-! # Crystalline Frobenius -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineFrobenius

noncomputable section

/-!
# p-semilinear Frobenius on actual crystalline cohomology

Absolute scheme Frobenius induces pullback to the twisted Witt base.
The proved base-twist transport returns it to the original cohomology,
semilinearly over Witt Frobenius. The proved big-to-small equivalence
and scalar extension give the operator on rational crystalline cohomology.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.PeriodInvariants.WittFrobeniusGeometry
open OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers

variable (p : ℕ) [Fact p.Prime]
variable (k : Type u) [Field k] [CharP k p] [PerfectRing k p]
variable (X : Over (Spec (CommRingCat.of k)))

local notation "W" => WittVector p k
local notation "K₀" => FractionRing W
local notation "φ" => WittVector.frobeniusEquiv p k
local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X

abbrev BigIntegralCohomology (n : ℕ) :=
  IntegralComparison.BigCrystallineCohomology.Cohomology
    (p := p) (J := Ideal.span {(p : W)}) (δ := γ) f n

def bigFrobenius (n : ℕ) : BigIntegralCohomology p k X n →ₛₗ[(φ).toRingHom]
    BigIntegralCohomology p k X n := by
  let F := (CrystallineTwistCohomology.cohomologyMap
    (p := p) (δ := γ) φ (IntegralComparison.Witt.Crystalline.wittFrobeniusDP p k).isDPMorphism
    (WittFrobeniusGeometry.inverse_isDPMorphism p k) (WittFrobeniusGeometry.schemeFrobenius_over p k X) n).comp
      (IntegralComparison.BigCrystallineCohomology.pullback (p := p) (J := Ideal.span {(p : W)}) (δ := γ)
        (WittFrobeniusGeometry.schemeFrobenius p k X) rfl n)
  refine { toFun := F, map_add' := F.map_add, map_smul' := ?_ }
  intro b x
  exact F.map_smulₛₗ (ULift.up b : ULift.{u + 1} W) x

variable [IsSeparated X.hom]

def integralFrobenius (n : ℕ) : IntegralComparison.Witt.Crystalline.integralCohomology p k X n →ₛₗ[(φ).toRingHom]
    IntegralComparison.Witt.Crystalline.integralCohomology p k X n :=
  (IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt p k X n).toLinearMap.comp
    ((bigFrobenius p k X n).comp
      (IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt p k X n).symm.toLinearMap)

theorem integral_intertwines (n : ℕ) (x : BigIntegralCohomology p k X n) :
    integralFrobenius p k X n (IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt p k X n x) =
      IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt p k X n (bigFrobenius p k X n x) := by
  change IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt p k X n
      (bigFrobenius p k X n ((IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt p k X n).symm
        (IntegralComparison.Global.Crystalline.Comparison.integralEquivWitt p k X n x))) = _
  rw [LinearEquiv.symm_apply_apply]

omit X [IsSeparated X.hom] in
def scalarFrobenius : K₀ ≃+* K₀ := IsFractionRing.ringEquivOfRingEquiv φ

omit X [IsSeparated X.hom] in
theorem scalarFrobenius_algebraMap (w : W) :
    scalarFrobenius p k (algebraMap W K₀ w) = algebraMap W K₀ (φ w) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ w

def rationalFrobenius (n : ℕ) : IntegralComparison.Witt.Crystalline.rationalCohomology p k X n →ₛₗ[(scalarFrobenius p k).toRingHom]
    IntegralComparison.Witt.Crystalline.rationalCohomology p k X n :=
  SemilinearBaseChange.baseChange (φ).toRingHom (scalarFrobenius p k).toRingHom
    (scalarFrobenius_algebraMap p k) (integralFrobenius p k X n)

theorem rationalFrobenius_tmul (n : ℕ) (a : K₀) (x : IntegralComparison.Witt.Crystalline.integralCohomology p k X n) :
    rationalFrobenius p k X n (a ⊗ₜ[W] x) =
      scalarFrobenius p k a ⊗ₜ[W] integralFrobenius p k X n x := rfl

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.CrystallineFrobenius
