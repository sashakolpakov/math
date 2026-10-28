import OAI.NumberTheory.Quaternion.Arithmetic.Norm

/-! # Finite Kernel Representatives -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.FiniteKernelRepresentatives

noncomputable section

/-! A finite collection of homomorphism values admits finitely many
representatives modulo the kernel. -/

open scoped Classical _root_.Quaternion
open Set

theorem finite_kernel_representatives {H K : Type*} [Group H] [Group K]
    (f : H →* K) (T : Set K) (hT : T.Finite) :
    ∃ R : Set H, R.Finite ∧ ∀ x : H, f x ∈ T →
      ∃ r ∈ R, ∃ q : f.ker, q.val * r = x := by
  let S := T ∩ Set.range f
  choose r hr using fun c : S => c.property.2
  let R := Set.range r
  have : Finite S := (hT.subset inter_subset_left).to_subtype
  refine ⟨R, Set.finite_range r, ?_⟩
  intro x hx
  let c : S := ⟨f x, hx, ⟨x, rfl⟩⟩
  have hker : x * (r c)⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hr c]
    exact mul_inv_cancel (f x)
  exact ⟨r c, Set.mem_range_self c, ⟨x * (r c)⁻¹, hker⟩, inv_mul_cancel_right x (r c)⟩

theorem quaternion_finite_norm_representatives {F : Type*} [Field F] (a b : F)
    (T : Set F) (hT : T.Finite) :
    ∃ R : Set (QuaternionAlgebra F a 0 b)ˣ, R.Finite ∧
      ∀ x : (QuaternionAlgebra F a 0 b)ˣ, Norm.quaternionNorm a b x.val ∈ T →
        ∃ r ∈ R, ∃ q : (Norm.quaternionUnitNorm a b).ker, q.val * r = x := by
  exact finite_kernel_representatives (Norm.quaternionUnitNorm a b) (Units.val ⁻¹' T)
    (hT.preimage Units.val_injective.injOn)

end

end OAI.NumberTheory.Quaternion.Arithmetic.FiniteKernelRepresentatives
