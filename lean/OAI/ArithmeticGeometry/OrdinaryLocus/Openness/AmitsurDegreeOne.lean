import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Amitsur Degree One -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmitsurDegreeOne.Construction

noncomputable section

/-! Exactness in degree one of the faithfully flat Amitsur complex. -/

open scoped TensorProduct

universe u v w

variable (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    (M : Type w) [AddCommGroup M] [Module R M]

def amitsurD0 : B ⊗[R] M →ₗ[R] B ⊗[R] (B ⊗[R] M) :=
  TensorProduct.mk R B (B ⊗[R] M) 1 - (TensorProduct.mk R B M 1).lTensor B

def amitsurD1 : B ⊗[R] (B ⊗[R] M) →ₗ[R] B ⊗[R] (B ⊗[R] (B ⊗[R] M)) :=
  TensorProduct.mk R B (B ⊗[R] (B ⊗[R] M)) 1 -
    (TensorProduct.mk R B (B ⊗[R] M) 1).lTensor B +
      ((TensorProduct.mk R B M 1).lTensor B).lTensor B

theorem amitsurD0_tmul (b : B) (m : M) :
    amitsurD0 R B M (b ⊗ₜ[R] m) = 1 ⊗ₜ[R] (b ⊗ₜ[R] m) - b ⊗ₜ[R] (1 ⊗ₜ[R] m) := by
  simp [amitsurD0]

theorem amitsurD1_tmul (a b : B) (m : M) :
    amitsurD1 R B M (a ⊗ₜ[R] (b ⊗ₜ[R] m)) =
      1 ⊗ₜ[R] (a ⊗ₜ[R] (b ⊗ₜ[R] m)) - a ⊗ₜ[R] (1 ⊗ₜ[R] (b ⊗ₜ[R] m)) +
        a ⊗ₜ[R] (b ⊗ₜ[R] (1 ⊗ₜ[R] m)) := by
  simp [amitsurD1]

def amitsurContract : B ⊗[R] (B ⊗[R] M) →ₗ[R] B ⊗[R] M :=
  TensorProduct.map (Algebra.TensorProduct.lmul' R : B ⊗[R] B →ₐ[R] B).toLinearMap
      (LinearMap.id : M →ₗ[R] M) ∘ₗ (TensorProduct.assoc R B B M).symm.toLinearMap

theorem amitsurContract_tmul (a b : B) (m : M) :
    amitsurContract R B M (a ⊗ₜ[R] (b ⊗ₜ[R] m)) = (a * b) ⊗ₜ[R] m := by
  simp [amitsurContract]

theorem amitsurD1_comp_D0 : (amitsurD1 R B M) ∘ₗ (amitsurD0 R B M) = 0 := by
  ext b m
  simp [amitsurD0_tmul, amitsurD1_tmul]

theorem amitsur_degreeOne_contraction :
    (amitsurD0 R B M).lTensor B ∘ₗ amitsurContract R B (B ⊗[R] M) +
      amitsurContract R B (B ⊗[R] (B ⊗[R] M)) ∘ₗ (amitsurD1 R B M).lTensor B =
        LinearMap.id := by
  ext a b c m
  simp [amitsurD0_tmul, amitsurD1_tmul, amitsurContract_tmul,
    TensorProduct.tmul_sub, TensorProduct.tmul_add]

theorem amitsur_exact_degreeOne [Module.FaithfullyFlat R B] :
    Function.Exact (amitsurD0 R B M) (amitsurD1 R B M) := by
  apply Module.FaithfullyFlat.lTensor_reflects_exact R B
  intro z
  constructor
  · intro hz
    refine ⟨amitsurContract R B (B ⊗[R] M) z, ?_⟩
    have h := LinearMap.congr_fun (amitsur_degreeOne_contraction R B M) z
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, hz, map_zero, add_zero,
      LinearMap.id_apply] using h
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f ↦ f.lTensor B) (amitsurD1_comp_D0 R B M)
    have hz := LinearMap.congr_fun h y
    simpa only [LinearMap.lTensor_comp_apply, LinearMap.lTensor_zero, LinearMap.zero_apply] using hz

theorem amitsurD0_comp_unit :
    amitsurD0 R B M ∘ₗ TensorProduct.mk R B M 1 = 0 := by
  ext m
  simp [amitsurD0_tmul]

theorem amitsur_degreeZero_contraction :
    (TensorProduct.mk R B M 1).lTensor B ∘ₗ amitsurContract R B M +
      amitsurContract R B (B ⊗[R] M) ∘ₗ (amitsurD0 R B M).lTensor B = LinearMap.id := by
  ext a b m
  simp [amitsurD0_tmul, amitsurContract_tmul, TensorProduct.tmul_sub]

theorem amitsur_exact_degreeZero [Module.FaithfullyFlat R B] :
    Function.Exact (TensorProduct.mk R B M 1) (amitsurD0 R B M) := by
  apply Module.FaithfullyFlat.lTensor_reflects_exact R B
  intro z
  constructor
  · intro hz
    refine ⟨amitsurContract R B M z, ?_⟩
    have h := LinearMap.congr_fun (amitsur_degreeZero_contraction R B M) z
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, hz, map_zero, add_zero,
      LinearMap.id_apply] using h
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f ↦ f.lTensor B) (amitsurD0_comp_unit R B M)
    have hz := LinearMap.congr_fun h y
    simpa only [LinearMap.lTensor_comp_apply, LinearMap.lTensor_zero, LinearMap.zero_apply] using hz

theorem amitsur_unit_injective [Module.FaithfullyFlat R B] :
    Function.Injective (TensorProduct.mk R B M 1) :=
  Module.FaithfullyFlat.tensorProduct_mk_injective M

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.AmitsurDegreeOne.Construction
