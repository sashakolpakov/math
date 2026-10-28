import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Grassmannian.Incidence

/-! # Schur Cokernel -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SchurCokernel.Grassmannian

noncomputable section

/-! An invertible pivot block gives a concrete cokernel presentation by its Schur complement, over arbitrary coefficient rings. -/

universe u v w z t

variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable {W : Type w} [AddCommGroup W] [Module R W]
variable {V' : Type z} [AddCommGroup V'] [Module R V']
variable {W' : Type t} [AddCommGroup W'] [Module R W']

def schurComplement (A : V ≃ₗ[R] V') (B : W →ₗ[R] V')
    (C : V →ₗ[R] W') (D : W →ₗ[R] W') : W →ₗ[R] W' :=
  D - C.comp (A.symm.toLinearMap.comp B)

def schurProjection (A : V ≃ₗ[R] V') (C : V →ₗ[R] W') : V' × W' →ₗ[R] W' :=
  LinearMap.snd R V' W' - C.comp (A.symm.toLinearMap.comp (LinearMap.fst R V' W'))

theorem schurProjection_apply (A : V ≃ₗ[R] V') (C : V →ₗ[R] W') (x : V' × W') :
    schurProjection A C x = x.2 - C (A.symm x.1) := rfl

theorem schurProjection_block (A : V ≃ₗ[R] V') (B : W →ₗ[R] V')
    (C : V →ₗ[R] W') (D : W →ₗ[R] W') (x : V × W) :
    schurProjection A C (Grassmannian.Incidence.blockLinearMap A.toLinearMap B C D x) = schurComplement A B C D x.2 := by
  change C x.1 + D x.2 - C (A.symm (A x.1 + B x.2)) = D x.2 - C (A.symm (B x.2))
  rw [map_add, LinearEquiv.symm_apply_apply, map_add]
  abel

theorem schurProjection_surjective (A : V ≃ₗ[R] V') (C : V →ₗ[R] W') :
    Function.Surjective (schurProjection A C) := by
  intro w
  exact ⟨(0, w), by simp [schurProjection_apply]⟩

theorem schurProjection_preimage_range (A : V ≃ₗ[R] V') (B : W →ₗ[R] V')
    (C : V →ₗ[R] W') (D : W →ₗ[R] W') :
    (schurComplement A B C D).range.comap (schurProjection A C) =
      (Grassmannian.Incidence.blockLinearMap A.toLinearMap B C D).range := by
  ext x
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨(A.symm (x.1 - B w), w), ?_⟩
    apply Prod.ext
    · change A (A.symm (x.1 - B w)) + B w = x.1
      rw [LinearEquiv.apply_symm_apply, sub_add_cancel]
    · change C (A.symm (x.1 - B w)) + D w = x.2
      change D w - C (A.symm (B w)) = x.2 - C (A.symm x.1) at hw
      rw [map_sub, map_sub]
      calc
        C (A.symm x.1) - C (A.symm (B w)) + D w =
            (D w - C (A.symm (B w))) + C (A.symm x.1) := by abel
        _ = x.2 := by rw [hw, sub_add_cancel]
  · rintro ⟨y, rfl⟩
    exact ⟨y.2, (schurProjection_block A B C D y).symm⟩

def schurCokernelMap (A : V ≃ₗ[R] V') (B : W →ₗ[R] V')
    (C : V →ₗ[R] W') (D : W →ₗ[R] W') :
    V' × W' →ₗ[R] W' ⧸ (schurComplement A B C D).range :=
  (schurComplement A B C D).range.mkQ.comp (schurProjection A C)

theorem schurCokernelMap_kernel (A : V ≃ₗ[R] V') (B : W →ₗ[R] V')
    (C : V →ₗ[R] W') (D : W →ₗ[R] W') :
    (schurCokernelMap A B C D).ker = (Grassmannian.Incidence.blockLinearMap A.toLinearMap B C D).range := by
  rw [schurCokernelMap, LinearMap.ker_comp, Submodule.ker_mkQ]
  exact schurProjection_preimage_range A B C D

def schurCokernelEquiv (A : V ≃ₗ[R] V') (B : W →ₗ[R] V')
    (C : V →ₗ[R] W') (D : W →ₗ[R] W') :
    ((V' × W') ⧸ (Grassmannian.Incidence.blockLinearMap A.toLinearMap B C D).range) ≃ₗ[R]
      W' ⧸ (schurComplement A B C D).range :=
  (Submodule.quotEquivOfEq _ _ (schurCokernelMap_kernel A B C D).symm).trans
    ((schurCokernelMap A B C D).quotKerEquivOfSurjective
      ((schurComplement A B C D).range.mkQ_surjective.comp (schurProjection_surjective A C)))

theorem schur_zero_exact (A : V ≃ₗ[R] V') (B : W →ₗ[R] V')
    (C : V →ₗ[R] W') (D : W →ₗ[R] W') (h : schurComplement A B C D = 0) :
    Function.Exact (Grassmannian.Incidence.blockLinearMap A.toLinearMap B C D) (schurProjection A C) := by
  apply LinearMap.exact_iff.mpr
  have he := schurProjection_preimage_range A B C D
  rw [h, LinearMap.range_zero] at he
  exact he

def schurZeroCokernelEquiv (A : V ≃ₗ[R] V') (B : W →ₗ[R] V')
    (C : V →ₗ[R] W') (D : W →ₗ[R] W') (h : schurComplement A B C D = 0) :
    ((V' × W') ⧸ (Grassmannian.Incidence.blockLinearMap A.toLinearMap B C D).range) ≃ₗ[R] W' :=
  (Submodule.quotEquivOfEq _ _ (LinearMap.exact_iff.mp (schur_zero_exact A B C D h)).symm).trans
    ((schurProjection A C).quotKerEquivOfSurjective (schurProjection_surjective A C))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SchurCokernel.Grassmannian
