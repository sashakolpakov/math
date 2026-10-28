import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IdealTensor.Intersection
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Maps

/-! # Adic Ideal Tensor Flatness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.AdicIdealTensorFlatness

noncomputable section

/-! Artin--Rees and Krull intersection reduce ideal-tensor flatness to
ideals containing powers of an ideal in the coefficient algebra's Jacobson
radical. -/

open TensorProduct

universe u v w
variable {B : Type u} [CommRing B]
variable (M : Type v) [AddCommGroup M] [Module B M]

theorem idealTensor_tmul_mem_smul (I J : Ideal B) (m : M) (r : I)
    (hr : r.val ∈ J • I) :
    m ⊗ₜ[B] r ∈ J • (⊤ : Submodule B (M ⊗[B] I)) := by
  have hr' : r ∈ J • (⊤ : Submodule B I) := (Submodule.mem_smul_top_iff J I r).mpr hr
  have ht : m ⊗ₜ[B] r ∈ (J • (⊤ : Submodule B I)).map (TensorProduct.mk B M I m) :=
    Submodule.mem_map_of_mem hr'
  rw [Submodule.map_smul''] at ht
  have hle : J • (⊤ : Submodule B I).map (TensorProduct.mk B M I m) ≤
      J • (⊤ : Submodule B (M ⊗[B] I)) := smul_mono_right J le_top
  exact hle ht

theorem idealTensor_inclusion_mem_smul (I J K : Ideal B) (hKI : K ≤ I)
    (hK : K ≤ J • I) (x : M ⊗[B] K) :
    (Submodule.inclusion hKI).lTensor M x ∈ J • (⊤ : Submodule B (M ⊗[B] I)) := by
  induction x with
  | tmul m r => exact idealTensor_tmul_mem_smul M I J m _ (hK r.property)
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

variable (S : Type w) [CommRing S] [Algebra B S]
variable [Module S M] [IsScalarTower B S M]
variable [IsNoetherianRing B] [IsNoetherianRing S] [Module.Finite S M]

theorem flat_of_adic_idealTensor_injective (J : Ideal B)
    (hJ : J.map (algebraMap B S) ≤ Ideal.jacobson ⊥)
    (h : ∀ (I : Ideal B) (n : ℕ),
      Function.Injective (IdealTensor.Obstruction.idealTensorMultiplication B B M (I ⊔ J ^ n))) :
    Module.Flat B M := by
  apply (IdealTensor.Obstruction.flat_iff_idealTensorObstructions_zero B B M).mpr
  intro I
  apply LinearMap.ker_eq_bot.mpr
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  let : Module.Finite S (M ⊗[B] I) := IdealTensor.Obstruction.idealTensorModule_finite B S M I (IsNoetherian.noetherian I)
  have hinter : (⨅ n : ℕ, (J.map (algebraMap B S)) ^ n •
      (⊤ : Submodule S (M ⊗[B] I))) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson _ hJ
  apply (Submodule.mem_bot (R := S)).mp
  rw [← hinter, Submodule.mem_iInf]
  intro n
  obtain ⟨c, hc⟩ := J.exists_pow_inf_eq_pow_smul I
  have hbound : I ⊓ J ^ (n + c) ≤ J ^ n • I := by
    have he := hc (n + c) (Nat.le_add_left c n)
    have htop (k : ℕ) : J ^ k • (⊤ : Submodule B B) = J ^ k := by
      rw [Ideal.smul_eq_mul, ← Ideal.one_eq_top, mul_one]
    rw [htop, htop, Nat.add_sub_cancel] at he
    rw [inf_comm, he]
    exact smul_mono_right _ inf_le_right
  obtain ⟨y, rfl⟩ := IdealTensor.Intersection.idealTensorObstruction_lifts_to_intersection M I (J ^ (n + c))
    (h I (n + c)) x hx
  have hy := idealTensor_inclusion_mem_smul M I (J ^ n) (I ⊓ J ^ (n + c))
    inf_le_left hbound y
  have he : (((J.map (algebraMap B S)) ^ n •
      (⊤ : Submodule S (M ⊗[B] I))).restrictScalars B) =
        J ^ n • (⊤ : Submodule B (M ⊗[B] I)) := by
    rw [← Ideal.map_pow, Ideal.smul_restrictScalars, Submodule.restrictScalars_top]
  rw [← he] at hy
  exact hy

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.AdicIdealTensorFlatness
