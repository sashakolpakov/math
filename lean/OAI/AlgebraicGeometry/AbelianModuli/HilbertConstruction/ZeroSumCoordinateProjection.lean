import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Zero Sum Coordinate Projection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroSumCoordinateProjection

noncomputable section

/-! Projection onto the zero-sum coordinate subspace, and coefficient
weights for functionals on that subspace. -/
open scoped BigOperators Classical

def coordinateSumLinearMap (m : ℕ) : (Fin m → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' a x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]

def zeroSumCoordinates (m : ℕ) : Submodule ℝ (Fin m → ℝ) := (coordinateSumLinearMap m).ker

def zeroSumProjection (m : ℕ) : (Fin m → ℝ) →ₗ[ℝ] (Fin m → ℝ) where
  toFun x i := x i - (∑ j, x j) / m
  map_add' x y := by
    ext i
    simp only [Pi.add_apply, Finset.sum_add_distrib, add_div]
    ring
  map_smul' a x := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, ← Finset.mul_sum]
    ring

theorem zeroSumProjection_mem {m : ℕ} (hm : 0 < m) (x : Fin m → ℝ) :
    zeroSumProjection m x ∈ zeroSumCoordinates m := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  change ∑ i, (x i - (∑ j, x j) / m) = 0
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [hm0]
  ring

def zeroSumProjectionTo {m : ℕ} (hm : 0 < m) :
    (Fin m → ℝ) →ₗ[ℝ] zeroSumCoordinates m :=
  (zeroSumProjection m).codRestrict (zeroSumCoordinates m) (zeroSumProjection_mem hm)

theorem zeroSumProjectionTo_subtype {m : ℕ} (hm : 0 < m) (x : zeroSumCoordinates m) :
    zeroSumProjectionTo hm x.val = x := by
  apply Subtype.ext
  ext i
  have hx : ∑ j, x.val j = 0 := x.property
  simp only [zeroSumProjectionTo, LinearMap.codRestrict_apply, zeroSumProjection,
    LinearMap.coe_mk, AddHom.coe_mk, hx, zero_div, sub_zero]

theorem zeroSumProjectionTo_one {m : ℕ} (hm : 0 < m) :
    zeroSumProjectionTo hm (fun _ => 1) = 0 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  apply Subtype.ext
  ext i
  change 1 - (∑ _ : Fin m, (1 : ℝ)) / m = 0
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    div_self hm0, sub_self]

theorem coordinateLinearMap_eq_sum {m : ℕ} (f : (Fin m → ℝ) →ₗ[ℝ] ℝ) (x : Fin m → ℝ) :
    f x = ∑ i, x i * f (Pi.single i 1) := by
  have hx : (∑ i, x i • Pi.single i (1 : ℝ)) = x := by
    ext j
    simp [Pi.single_apply]
  calc
    f x = f (∑ i, x i • Pi.single i 1) := congrArg f hx.symm
    _ = ∑ i, x i * f (Pi.single i 1) := by simp only [map_sum, map_smul, smul_eq_mul]

def zeroSumFunctionalWeights {m : ℕ} (hm : 0 < m) (f : zeroSumCoordinates m →ₗ[ℝ] ℝ) : Fin m → ℝ :=
  fun i => f (zeroSumProjectionTo hm (Pi.single i 1))

theorem zeroSumFunctionalWeights_sum {m : ℕ} (hm : 0 < m) (f : zeroSumCoordinates m →ₗ[ℝ] ℝ) :
    ∑ i, zeroSumFunctionalWeights hm f i = 0 := by
  have h := coordinateLinearMap_eq_sum (f.comp (zeroSumProjectionTo hm)) (fun _ => 1)
  simpa only [LinearMap.comp_apply, zeroSumProjectionTo_one hm, map_zero, one_mul,
    zeroSumFunctionalWeights] using h.symm

theorem zeroSumFunctionalWeights_eval {m : ℕ} (hm : 0 < m)
    (f : zeroSumCoordinates m →ₗ[ℝ] ℝ) (x : Fin m → ℝ) :
    f (zeroSumProjectionTo hm x) = ∑ i, x i * zeroSumFunctionalWeights hm f i :=
  coordinateLinearMap_eq_sum (f.comp (zeroSumProjectionTo hm)) x

theorem zeroSumFunctionalWeights_ne_zero {m : ℕ} (hm : 0 < m)
    (f : zeroSumCoordinates m →ₗ[ℝ] ℝ) (hf : f ≠ 0) : zeroSumFunctionalWeights hm f ≠ 0 := by
  intro hz
  apply hf
  ext x
  rw [← zeroSumProjectionTo_subtype hm x, zeroSumFunctionalWeights_eval]
  simp only [hz, Pi.zero_apply, mul_zero, Finset.sum_const_zero, LinearMap.zero_apply]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroSumCoordinateProjection
