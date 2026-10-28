import OAI.NumberTheory.ArithmeticGroups.Lattices.AlgebraicSpecialization

/-! # Tensor Domain Specialization -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.TensorDomainSpecialization.Construction

noncomputable section

section

/-! A nonzero tensor over a finitely generated coefficient domain stays
nonzero under a suitable specialization to the algebraic closure. -/

open scoped Classical TensorProduct

theorem tensor_basis_coordinate_map
    {k A B C ι : Type*} [Field k] [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] [CommRing C] [Algebra k C]
    (b : Module.Basis ι k A) (φ : B →ₐ[k] C) (x : B ⊗[k] A) (i : ι) :
    (b.baseChange C).repr (Algebra.TensorProduct.map φ (AlgHom.id k A) x) i =
      φ ((b.baseChange B).repr x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul a c => simp [Module.Basis.baseChange_repr_tmul]
  | add x y hx hy => simp [hx, hy]

theorem exists_nonzero_tensor_specialization
    (k A B : Type*) [Field k] [CommRing A] [Algebra k A]
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

end

section

/-! Simultaneous specialization of two nonzero tensors, used to
preserve irreducibility under field extension. -/

open scoped Classical TensorProduct

theorem exists_nonzero_pair_tensor_specialization
    (k A B : Type*) [Field k] [CommRing A] [Algebra k A]
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
    (k A B : Type*) [Field k] [CommRing A] [Algebra k A]
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

/-! Absence of zero divisors after extension to the algebraic closure
implies the same after every extension field. -/

open scoped Classical TensorProduct

theorem subalgebra_baseChange_mono
    {k A B : Type*} [Field k] [CommRing A] [Algebra k A] [CommRing B] [Algebra k B]
    {C D : Subalgebra k B} (hCD : C ≤ D) : C.baseChange A ≤ D.baseChange A := by
  rintro x ⟨y, rfl⟩
  refine ⟨Algebra.TensorProduct.map (AlgHom.id A A) (Subalgebra.inclusion hCD) y, ?_⟩
  induction y using TensorProduct.inductionOn with
  | tmul a b => rfl
  | add x y hx hy =>
    simp only [map_add]
    exact congrArg₂ (· + ·) hx hy

theorem tensor_field_noZeroDivisors_of_algClosure
    (k K A : Type*) [Field k] [Field K] [Algebra k K]
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
  let : NoZeroDivisors (B ⊗[k] A) := finiteType_domain_tensor_noZeroDivisors_of_algClosure k A B
  let e := Algebra.TensorProduct.comm k A B
  have he : e u * e v = 0 := by rw [← map_mul, huv, map_zero]
  rcases mul_eq_zero.mp he with he | he
  · have hu0 : u = 0 := e.injective (he.trans e.map_zero.symm)
    exact Or.inl (hu.symm.trans ((congrArg f hu0).trans f.map_zero))
  · have hv0 : v = 0 := e.injective (he.trans e.map_zero.symm)
    exact Or.inr (hv.symm.trans ((congrArg f hv0).trans f.map_zero))

theorem field_tensor_domain_of_algClosure
    (k K A : Type*) [Field k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] [IsDomain (AlgebraicClosure k ⊗[k] A)] :
    IsDomain (K ⊗[k] A) := by
  let : Nontrivial A :=
    (Algebra.TensorProduct.includeRight : A →ₐ[k] AlgebraicClosure k ⊗[k] A).toRingHom.domain_nontrivial
  let : NoZeroDivisors (A ⊗[k] K) := tensor_field_noZeroDivisors_of_algClosure k K A
  let : NoZeroDivisors (K ⊗[k] A) :=
    (Algebra.TensorProduct.comm k K A).toMulEquiv.noZeroDivisors
  exact NoZeroDivisors.to_isDomain _

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.TensorDomainSpecialization.Construction
