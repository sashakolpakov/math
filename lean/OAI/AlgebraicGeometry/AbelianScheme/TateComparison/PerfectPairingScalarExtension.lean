import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.IntegralPairingLattices
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.TensorLattice
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! # Perfect Pairing Scalar Extension -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PerfectPairingScalarExtension

noncomputable section

/-! Scalar extension of an integral perfect pairing is nondegenerate,
and the actual integral image is its own dual lattice. -/

open scoped TensorProduct

variable {R K V W I : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [Fintype I] [DecidableEq I]

theorem linearMap_matrix_det_unit_of_bijective
    (bV : Module.Basis I R V) (bW : Module.Basis I R W) (f : V →ₗ[R] W)
    (hf : Function.Bijective f) : IsUnit (LinearMap.toMatrix bV bW f).det := by
  let e := LinearEquiv.ofBijective f hf
  have hi : f.comp e.symm.toLinearMap = LinearMap.id := by
    ext y
    exact e.apply_symm_apply y
  have hm : LinearMap.toMatrix bV bW f * LinearMap.toMatrix bW bV e.symm.toLinearMap = 1 := by
    rw [← LinearMap.toMatrix_comp, hi, LinearMap.toMatrix_id]
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_one] at hd
  exact isUnit_iff_exists_inv.mpr ⟨_, hd⟩

theorem perfectBilinear_matrix_det_unit (b : Module.Basis I R V)
    (B : LinearMap.BilinForm R V) (hB : B.IsPerfPair) :
    IsUnit (LinearMap.BilinForm.toMatrix b B).det := by
  let := hB
  have hM : LinearMap.toMatrix b b.dualBasis B = (LinearMap.BilinForm.toMatrix b B).transpose := by
    ext i j
    simp only [LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr,
      LinearMap.BilinForm.toMatrix_apply, Matrix.transpose_apply]
  have h := linearMap_matrix_det_unit_of_bijective b b.dualBasis B (LinearMap.IsPerfPair.bijective_left B)
  rw [hM, Matrix.det_transpose] at h
  exact h

theorem integralBilinearBaseChange_matrix (b : Module.Basis I R V) (B : LinearMap.BilinForm R V) :
    LinearMap.BilinForm.toMatrix (b.baseChange K) (B.baseChange K) =
      (algebraMap R K).mapMatrix (LinearMap.BilinForm.toMatrix b B) := by
  ext i j
  simp only [LinearMap.BilinForm.toMatrix_apply, Module.Basis.baseChange_apply,
    LinearMap.BilinForm.baseChange_tmul, one_mul, RingHom.mapMatrix_apply, Matrix.map_apply,
    Algebra.algebraMap_eq_smul_one]

theorem perfectBilinearBaseChange_nondegenerate (b : Module.Basis I R V)
    (B : LinearMap.BilinForm R V) (hB : B.IsPerfPair) : (B.baseChange K).Nondegenerate := by
  apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (b.baseChange K)).mpr
  rw [integralBilinearBaseChange_matrix, ← RingHom.map_det]
  exact ((perfectBilinear_matrix_det_unit b B hB).map (algebraMap R K)).ne_zero

variable [IsDomain R] [Module.IsTorsionFree R K]

theorem tensorIntegralImage_self_dual (b : Module.Basis I R V)
    (B : LinearMap.BilinForm R V) (hB : B.IsPerfPair)
    (hι : Function.Injective (TensorProduct.mk R K V 1)) :
    (B.baseChange K).dualSubmodule (TensorProduct.mk R K V 1).range =
      (TensorProduct.mk R K V 1).range := by
  let L := (TensorProduct.mk R K V 1).range
  let e : V ≃ₗ[R] L := LinearEquiv.ofInjective (TensorProduct.mk R K V 1) hι
  have hval (y x : V) : (B.baseChange K) (e y).val (e x).val = algebraMap R K (B y x) := by
    change (B.baseChange K) (1 ⊗ₜ[R] y) (1 ⊗ₜ[R] x) = _
    rw [LinearMap.BilinForm.baseChange_tmul, one_mul, Algebra.algebraMap_eq_smul_one]
  let := hB
  exact (IntegralPairingLattices.integralPairing_image_eq_dual (B.baseChange K) L L e e B hval
    (LinearMap.IsPerfPair.bijective_left B) (perfectBilinearBaseChange_nondegenerate b B hB)
    (TensorLattice.tensorIntegralImage_isLattice (K := K) b).span_eq_top).symm

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.PerfectPairingScalarExtension
