import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Algebra.Category.ModuleCat.Basic

/-! # Dual Normalization -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.DualNormalization.Cycles

noncomputable section

/-!
# Dual normalization of a module identified with its coefficient field

An actual linear equivalence `e: V ≃ₗ[F] F` identifies the dual of `V` with `F`
by evaluating a functional on `e.symm 1`. This is the composite of mathlib's
dual-map equivalence and its equivalence between linear maps out of the scalar
ring and their values at `1`. The inverse sends a scalar to that scalar times
`e.toLinearMap`, so no choice of basis or generator is introduced.
-/

universe uF uV

variable {F : Type uF} [Field F]
variable {V : Type uV} [AddCommGroup V] [Module F V]

/-- Normalize a dual functional by its value on the vector corresponding to `1`. -/
def dualNormalizationEquiv (e : V ≃ₗ[F] F) : Module.Dual F V ≃ₗ[F] F :=
  e.symm.dualMap.trans (LinearMap.ringLmapEquivSelf F F F)

@[simp]
theorem dualNormalizationEquiv_apply (e : V ≃ₗ[F] F) (φ : Module.Dual F V) :
    dualNormalizationEquiv e φ = φ (e.symm 1) :=
  rfl

@[simp]
theorem dualNormalizationEquiv_symm_apply (e : V ≃ₗ[F] F) (a : F) :
    (dualNormalizationEquiv e).symm a = a • e.toLinearMap := by
  ext v
  change e v * a = a * e v
  exact mul_comm _ _

@[simp]
theorem dualNormalizationEquiv_symm_one (e : V ≃ₗ[F] F) :
    (dualNormalizationEquiv e).symm 1 = e.toLinearMap := by
  rw [dualNormalizationEquiv_symm_apply, one_smul]

@[simp]
theorem dualNormalizationEquiv_toLinearMap (e : V ≃ₗ[F] F) :
    dualNormalizationEquiv e e.toLinearMap = 1 := by
  simp

/-- Evaluation of the functional of any prescribed normalization. -/
theorem dualNormalizationEquiv_symm_apply_apply (e : V ≃ₗ[F] F) (a : F) (v : V) :
    (dualNormalizationEquiv e).symm a v = a * e v := by
  rw [dualNormalizationEquiv_symm_apply]
  rfl

/-- Every functional is its normalization times the original coordinate map. -/
theorem dual_eq_normalization_smul (e : V ≃ₗ[F] F) (φ : Module.Dual F V) :
    φ = dualNormalizationEquiv e φ • e.toLinearMap := by
  rw [← dualNormalizationEquiv_symm_apply]
  exact ((dualNormalizationEquiv e).symm_apply_apply φ).symm

theorem dual_apply_eq_normalization_mul (e : V ≃ₗ[F] F)
    (φ : Module.Dual F V) (v : V) :
    φ v = dualNormalizationEquiv e φ * e v :=
  congrArg (fun ψ : Module.Dual F V => ψ v) (dual_eq_normalization_smul e φ)

/-- The coefficient of a functional is determined by evaluation on `e.symm 1`. -/
theorem dual_eq_smul_iff (e : V ≃ₗ[F] F) (φ : Module.Dual F V) (a : F) :
    φ = a • e.toLinearMap ↔ φ (e.symm 1) = a := by
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    calc
      φ = dualNormalizationEquiv e φ • e.toLinearMap := dual_eq_normalization_smul e φ
      _ = a • e.toLinearMap := by rw [dualNormalizationEquiv_apply, h]

/-- The original coordinate map is the unique functional normalized to `1`. -/
theorem dual_normalization_eq_one_iff (e : V ≃ₗ[F] F) (φ : Module.Dual F V) :
    φ (e.symm 1) = 1 ↔ φ = e.toLinearMap := by
  simpa only [one_smul] using (dual_eq_smul_iff e φ 1).symm

theorem dual_existsUnique_smul (e : V ≃ₗ[F] F) (φ : Module.Dual F V) :
    ∃! a : F, φ = a • e.toLinearMap := by
  refine ⟨dualNormalizationEquiv e φ, dual_eq_normalization_smul e φ, ?_⟩
  intro a ha
  exact ((dual_eq_smul_iff e φ a).mp ha).symm

/-- Evaluation on the normalized vector detects equality of dual functionals. -/
theorem dual_eq_of_normalization_eq (e : V ≃ₗ[F] F) {φ ψ : Module.Dual F V}
    (h : φ (e.symm 1) = ψ (e.symm 1)) : φ = ψ :=
  (dualNormalizationEquiv e).injective h

/-- The dual of an actual zero module is zero. -/
theorem dual_isZero_of_isZero
    (hV : CategoryTheory.Limits.IsZero (ModuleCat.of F V)) :
    CategoryTheory.Limits.IsZero (ModuleCat.of F (Module.Dual F V)) := by
  let : Subsingleton V := ModuleCat.subsingleton_of_isZero hV
  exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.DualNormalization.Cycles
