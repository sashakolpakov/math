import OAI.ArithmeticGeometry.Models.SpreadingOut.AlgebraicSpecialization
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.RingTheory.Flat.Basic

/-! # Tensor Specialization -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.TensorSpecialization.Construction

noncomputable section

/-! A nonzero tensor over a finitely generated coefficient domain stays
nonzero under a suitable specialization to the algebraic closure. -/

universe u
open scoped Classical TensorProduct

theorem tensor_basis_coordinate_map
    {k A B C ι : Type u} [Field k] [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]
    (b : Module.Basis ι k A) (φ : B →ₐ[k] C) (x : B ⊗[k] A) (i : ι) :
    (b.baseChange C).repr (Algebra.TensorProduct.map φ (AlgHom.id k A) x) i =
      φ ((b.baseChange B).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul a c => simp [Module.Basis.baseChange_repr_tmul]
  | add x y hx hy => simp [hx, hy]

theorem exists_nonzero_tensor_specialization
    (k A B : Type u) [Field k] [CommRing A] [Algebra k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    {x : B ⊗[k] A} (hx : x ≠ 0) :
    ∃ φ : B →ₐ[k] AlgebraicClosure k,
      Algebra.TensorProduct.map φ (AlgHom.id k A) x ≠ 0 := by
  let b := Module.Free.chooseBasis k A
  have hc : ∃ i, (b.baseChange B).repr x i ≠ 0 := by
    by_contra h
    apply hx
    apply (b.baseChange B).repr.injective
    ext i
    simpa only [map_zero, Finsupp.zero_apply] using not_exists_not.mp h i
  obtain ⟨i, hi⟩ := hc
  obtain ⟨φ, hφ⟩ := AlgebraicSpecialization.Construction.finiteType_specialization_nonzero k B hi
  refine ⟨φ, fun hzero => hφ ?_⟩
  have he := congrArg (fun z => (b.baseChange (AlgebraicClosure k)).repr z i) hzero
  simpa only [tensor_basis_coordinate_map, map_zero, Finsupp.zero_apply] using he

theorem exists_nonzero_pair_tensor_specialization
    (k A B : Type u) [Field k] [CommRing A] [Algebra k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    {x y : B ⊗[k] A} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ φ : B →ₐ[k] AlgebraicClosure k,
      Algebra.TensorProduct.map φ (AlgHom.id k A) x ≠ 0 ∧
      Algebra.TensorProduct.map φ (AlgHom.id k A) y ≠ 0 := by
  let b := Module.Free.chooseBasis k A
  have hc (z : B ⊗[k] A) (hz : z ≠ 0) : ∃ i, (b.baseChange B).repr z i ≠ 0 := by
    by_contra h
    apply hz
    apply (b.baseChange B).repr.injective
    ext i
    simpa only [map_zero, Finsupp.zero_apply] using not_exists_not.mp h i
  obtain ⟨i, hi⟩ := hc x hx
  obtain ⟨j, hj⟩ := hc y hy
  obtain ⟨φ, hφ⟩ := AlgebraicSpecialization.Construction.finiteType_specialization_nonzero k B (mul_ne_zero hi hj)
  rw [map_mul] at hφ
  obtain ⟨hφi, hφj⟩ := mul_ne_zero_iff.mp hφ
  have hd (z : B ⊗[k] A) (i) (hi : φ ((b.baseChange B).repr z i) ≠ 0) :
      Algebra.TensorProduct.map φ (AlgHom.id k A) z ≠ 0 := by
    intro hzero
    apply hi
    have he := congrArg (fun w => (b.baseChange (AlgebraicClosure k)).repr w i) hzero
    simpa only [tensor_basis_coordinate_map, map_zero, Finsupp.zero_apply] using he
  exact ⟨φ, hd x i hφi, hd y j hφj⟩

theorem finiteType_domain_tensor_noZeroDivisors_of_algClosure
    (k A B : Type u) [Field k] [CommRing A] [Algebra k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [NoZeroDivisors (AlgebraicClosure k ⊗[k] A)] : NoZeroDivisors (B ⊗[k] A) := by
  constructor
  intro x y hxy
  by_contra h
  obtain ⟨hx, hy⟩ := not_or.mp h
  obtain ⟨φ, hφx, hφy⟩ := exists_nonzero_pair_tensor_specialization k A B hx hy
  have he := congrArg (Algebra.TensorProduct.map φ (AlgHom.id k A)) hxy
  rw [map_mul, map_zero] at he
  exact (mul_ne_zero hφx hφy) he

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.TensorSpecialization.Construction
