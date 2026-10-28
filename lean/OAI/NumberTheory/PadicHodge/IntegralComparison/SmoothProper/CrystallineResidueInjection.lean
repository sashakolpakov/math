import OAI.NumberTheory.PadicHodge.IntegralComparison.ZeroLevel.GlobalFunctionLinear
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechInverseLimit
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechFiniteness

/-! # Crystalline Residue Injection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineResidueInjection

noncomputable section

/-! Reduction modulo p of the original integral crystalline degree-zero cohomology injects into actual global regular functions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "A" => (fun n : ℕ => ModuleCat.carrier
  (HomologicalComplex.homology (WittCechTransitionData.complex p k X n) 0))
local notation "t" => (fun n : ℕ => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CechScalarSystem.map p k X n (n + 1) (Nat.le_succ n) 0)
local notation "L" => OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarInverseResidue.compatible R A t
local notation "M" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.integralCohomology p k X 0

def cechEvaluation : L →ₗ[R] ZeroLevel.GlobalFunctionLinear.coefficientModule p k X :=
  (ZeroLevel.GlobalFunctionLinear.cohomologyMap p k X).comp
    ((WittCechLinearEquiv.equivalence p k X 0 0).toLinearMap.comp
      (ScalarInverseResidue.evaluation R A t))

theorem cechEvaluation_zero (x : L) :
    cechEvaluation p k X x = 0 ↔ ScalarInverseResidue.evaluation R A t x = 0 := by
  exact ((ZeroLevel.GlobalFunctionLinear.cohomologyMap_injective p k X).eq_iff'
    (ZeroLevel.GlobalFunctionLinear.cohomologyMap p k X).map_zero).trans
      ((WittCechLinearEquiv.equivalence p k X 0 0).map_eq_zero_iff)

variable (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

include hprojective in
theorem cechEvaluation_kernel : LinearMap.ker (cechEvaluation p k X) =
    (Ideal.span {(p : R)}) • (⊤ : Submodule R L) := by
  have he : LinearMap.ker (cechEvaluation p k X) =
      LinearMap.ker (ScalarInverseResidue.evaluation R A t) := by
    ext x
    exact cechEvaluation_zero p k X x
  rw [he]
  let (n : ℕ) : Finite (A n) := CechScalarSystem.finite p k X hprojective n 0
  exact ScalarInverseResidue.kernel R (p : R) A t
    (fun n => CechScalarSystem.inclusion p k X n 0)
    (fun n => CechScalarSystem.map p k X 0 n (Nat.zero_le n) 0)
    (fun n x => CechScalarSystem.inclusion_map p k X n 0 x)
    (fun n x => CechScalarSystem.map_inclusion p k X n 0 x)
    (CechScalarSystem.identity p k X 0 0)
    (fun n x => CechScalarSystem.composition p k X 0 n (n + 1)
      (Nat.zero_le n) (Nat.le_succ n) 0 x)
    (fun n x => CechScalarSystem.exact p k X n 0 x)
    (fun x => by simpa only [zero_add, pow_one] using CechScalarSystem.power_zero p k X 0 0 x)

def integralEvaluation : M →ₗ[R] ZeroLevel.GlobalFunctionLinear.coefficientModule p k X :=
  (cechEvaluation p k X).comp (CechInverseLimit.integralEquiv p k X hprojective 0).toLinearMap

theorem integralEvaluation_kernel : LinearMap.ker (integralEvaluation p k X hprojective) =
    (Ideal.span {(p : R)}) • (⊤ : Submodule R M) := by
  let e : M ≃ₗ[R] L := CechInverseLimit.integralEquiv p k X hprojective 0
  have hL (x : L) : x ∈ (Ideal.span {(p : R)}) • (⊤ : Submodule R L) ↔ ∃ y : L, (p : R) • y = x := by
    simpa only [Principal.PowerModuleSequence.submodule, pow_one] using
      Principal.PowerModuleSequence.mem_submodule R L (p : R) 1 x
  have hM (x : M) : x ∈ (Ideal.span {(p : R)}) • (⊤ : Submodule R M) ↔ ∃ y : M, (p : R) • y = x := by
    simpa only [Principal.PowerModuleSequence.submodule, pow_one] using
      Principal.PowerModuleSequence.mem_submodule R M (p : R) 1 x
  ext x
  change cechEvaluation p k X (e x) = 0 ↔ _
  rw [← LinearMap.mem_ker, cechEvaluation_kernel p k X hprojective, hL, hM]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, e.injective ?_⟩
    exact (e.map_smul (p : R) (e.symm y)).trans
      ((congrArg (fun z => (p : R) • z) (e.apply_symm_apply y)).trans hy)
  · rintro ⟨y, rfl⟩
    exact ⟨e y, (e.map_smul (p : R) y).symm⟩

def map : (M ⧸ ((Ideal.span {(p : R)}) • (⊤ : Submodule R M))) →ₗ[R]
    ZeroLevel.GlobalFunctionLinear.coefficientModule p k X :=
  ((Ideal.span {(p : R)}) • (⊤ : Submodule R M)).liftQ (integralEvaluation p k X hprojective)
    (integralEvaluation_kernel p k X hprojective).ge

theorem injective : Function.Injective (map p k X hprojective) :=
  LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ (integralEvaluation p k X hprojective)
    (integralEvaluation_kernel p k X hprojective).ge (integralEvaluation_kernel p k X hprojective).le)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.CrystallineResidueInjection
