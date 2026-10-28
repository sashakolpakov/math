import OAI.ArithmeticGeometry.Models.SpreadingOut.TensorSpecialization
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-! # Tensor Domain -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.TensorDomain.Construction

noncomputable section

/-! Absence of zero divisors after extension to the algebraic closure
implies the same after every extension field. -/

universe u
open scoped Classical TensorProduct

theorem subalgebra_baseChange_mono
    {k A B : Type u} [Field k] [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    {C D : Subalgebra k B} (hCD : C ≤ D) : C.baseChange A ≤ D.baseChange A := by
  rintro x ⟨y, rfl⟩
  refine ⟨Algebra.TensorProduct.map (AlgHom.id A A) (Subalgebra.inclusion hCD) y, ?_⟩
  induction y using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy =>
    simp only [map_add]
    exact congrArg₂ (· + ·) hx hy

theorem tensor_field_noZeroDivisors_of_algClosure
    (k K A : Type u) [Field k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] [NoZeroDivisors (AlgebraicClosure k ⊗[k] A)] :
    NoZeroDivisors (A ⊗[k] K) := by
  constructor
  intro x y hxy
  obtain ⟨C, hC, hxC⟩ := exists_fg_and_mem_baseChange x
  obtain ⟨D, hD, hyD⟩ := exists_fg_and_mem_baseChange y
  let B := C ⊔ D
  let : Algebra.FiniteType k B := B.fg_iff_finiteType.mp (hC.sup hD)
  have hxB : x ∈ B.baseChange A := subalgebra_baseChange_mono le_sup_left hxC
  have hyB : y ∈ B.baseChange A := subalgebra_baseChange_mono le_sup_right hyD
  obtain ⟨u, hu⟩ := hxB
  obtain ⟨v, hv⟩ := hyB
  let f : A ⊗[k] B →ₐ[A] A ⊗[k] K := Algebra.TensorProduct.map (AlgHom.id A A) B.val
  change f u = x at hu
  change f v = y at hv
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap B.val.toLinearMap Subtype.val_injective
  have huv : u * v = 0 := hf (by rw [map_mul, hu, hv, hxy, map_zero])
  let : NoZeroDivisors (B ⊗[k] A) := TensorSpecialization.Construction.finiteType_domain_tensor_noZeroDivisors_of_algClosure k A B
  let e := Algebra.TensorProduct.comm k A B
  have he : e u * e v = 0 := by rw [← map_mul, huv, map_zero]
  rcases mul_eq_zero.mp he with he | he
  · have hu0 : u = 0 := e.injective (he.trans e.map_zero.symm)
    exact Or.inl (hu.symm.trans ((congrArg f hu0).trans f.map_zero))
  · have hv0 : v = 0 := e.injective (he.trans e.map_zero.symm)
    exact Or.inr (hv.symm.trans ((congrArg f hv0).trans f.map_zero))

theorem field_tensor_domain_of_algClosure
    (k K A : Type u) [Field k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] [IsDomain (AlgebraicClosure k ⊗[k] A)] :
    IsDomain (K ⊗[k] A) := by
  let : Nontrivial A :=
    (Algebra.TensorProduct.includeRight : A →ₐ[k] AlgebraicClosure k ⊗[k] A).toRingHom.domain_nontrivial
  let : NoZeroDivisors (A ⊗[k] K) := tensor_field_noZeroDivisors_of_algClosure k K A
  let : NoZeroDivisors (K ⊗[k] A) :=
    (Algebra.TensorProduct.comm k K A).toMulEquiv.noZeroDivisors
  exact NoZeroDivisors.to_isDomain _

theorem tensor_domain_over_algClosed
    (k K A : Type u) [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
    [CommRing A] [IsDomain A] [Algebra k A] : IsDomain (K ⊗[k] A) := by
  let e : AlgebraicClosure k ≃ₐ[k] k :=
    (AlgEquiv.ofBijective (Algebra.ofId k (AlgebraicClosure k))
      IsAlgClosed.algebraMap_bijective_of_isIntegral).symm
  have : IsDomain (AlgebraicClosure k ⊗[k] A) :=
    ((Algebra.TensorProduct.congr e (AlgEquiv.refl : A ≃ₐ[k] A)).trans
      (Algebra.TensorProduct.lid k A)).toMulEquiv.isDomain
  exact field_tensor_domain_of_algClosure k K A

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.TensorDomain.Construction
