import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.AlgebraKernelBaseChange

/-! # Tensor Unit Kernel -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.TensorUnitKernel

noncomputable section

/-! The kernel of the unit map into a tensor product is the extension
of the kernel of the original coefficient map. -/

open TensorProduct

universe u v w
variable (R : Type u) [CommRing R]
variable (A : Type v) [CommRing A] [Algebra R A] [Module.Flat R A]
variable (C : Type w) [CommRing C] [Algebra R C]

theorem flat_tensor_unit_kernel :
    RingHom.ker (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] C) =
      (RingHom.ker (algebraMap R C)).map (algebraMap R A) := by
  let g : R →ₐ[R] C := Algebra.ofId R C
  let e : A ⊗[R] R ≃ₐ[R] A := Algebra.TensorProduct.rid R R A
  have he : e.toRingHom.comp
      (Algebra.TensorProduct.includeRight : R →ₐ[R] A ⊗[R] R).toRingHom =
      algebraMap R A := by
    apply RingHom.ext
    intro r
    simp [e, Algebra.smul_def]
  apply le_antisymm
  · intro a ha
    change a ⊗ₜ[R] (1 : C) = 0 at ha
    have hz : a ⊗ₜ[R] (1 : R) ∈
        RingHom.ker (Algebra.TensorProduct.map (AlgHom.id R A) g) := by
      change (Algebra.TensorProduct.map (AlgHom.id R A) g) (a ⊗ₜ[R] (1 : R)) = 0
      simpa only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one] using ha
    rw [AlgebraKernelBaseChange.flat_tensor_algebra_kernel A g] at hz
    have hm := Ideal.mem_map_of_mem e.toRingHom hz
    change e (a ⊗ₜ[R] (1 : R)) ∈
      ((RingHom.ker g.toRingHom).map
        (Algebra.TensorProduct.includeRight : R →ₐ[R] A ⊗[R] R).toRingHom).map
          e.toRingHom at hm
    rw [Ideal.map_map, he] at hm
    simpa only [e, g, Algebra.TensorProduct.rid_tmul, one_smul] using! hm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] C)
      (algebraMap R A r) = 0
    change algebraMap R A r ⊗ₜ[R] (1 : C) = 0
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      Algebra.smul_def, mul_one, hr, TensorProduct.tmul_zero]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.TensorUnitKernel
