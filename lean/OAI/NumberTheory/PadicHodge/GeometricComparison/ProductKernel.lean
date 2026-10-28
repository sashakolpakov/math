import OAI.NumberTheory.PadicHodge.GeometricComparison.Linear

/-! # Product Kernel -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ProductKernel.ProductSubspace

noncomputable section

/-! The kernel of a product projection is the actual subspace in the first factor, including its induced filtration step. -/

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

def first (U : Submodule K (V × W)) : Submodule K V := U.comap (LinearMap.inl K V W)

def second (U : Submodule K (V × W)) : U →ₗ[K] W := (LinearMap.snd K V W).domRestrict U

def kernelEquiv (U : Submodule K (V × W)) : (second U).ker ≃ₗ[K] first U where
  toFun x := ⟨x.1.1.1, by
    change (x.1.1.1, 0) ∈ U
    have hx : x.1.1.2 = 0 := x.property
    have he : (x.1.1.1, 0) = x.1.1 := Prod.ext rfl hx.symm
    exact he.symm ▸ x.1.property⟩
  invFun x := ⟨⟨(x, 0), x.property⟩, rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl x.property.symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def filteredKernelEquiv (U : Submodule K (V × W)) (P : Submodule K V) (Q : Submodule K W) :
    ((second U).ker ⊓ (P.prod Q).comap U.subtype : Submodule K U) ≃ₗ[K]
      (first U ⊓ P : Submodule K V) where
  toFun x := ⟨x.1.1.1, by
    constructor
    · change (x.1.1.1, 0) ∈ U
      have hx : x.1.1.2 = 0 := x.2.1
      have he : (x.1.1.1, 0) = x.1.1 := Prod.ext rfl hx.symm
      exact he.symm ▸ x.1.property
    · exact x.2.2.1⟩
  invFun x := ⟨⟨(x, 0), x.2.1⟩, rfl, x.2.2, Q.zero_mem⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl x.2.1.symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem first_stable (φ : Module.End K V) (ψ : Module.End K W) (U : Submodule K (V × W))
    (hU : U ≤ U.comap (LinearMap.prodMap φ ψ)) : first U ≤ (first U).comap φ := by
  intro x hx
  have h := hU hx
  change (φ x, ψ 0) ∈ U at h
  change (φ x, 0) ∈ U
  simpa only [ψ.map_zero] using h

theorem second_intertwines (φ : Module.End K V) (ψ : Module.End K W) (U : Submodule K (V × W))
    (hU : U ≤ U.comap (LinearMap.prodMap φ ψ)) (x : U) :
    second U ((LinearMap.prodMap φ ψ).restrict hU x) = ψ (second U x) := rfl

theorem second_filtered (U : Submodule K (V × W)) (P : Submodule K V) (Q : Submodule K W) :
    ((P.prod Q).comap U.subtype).map (second U) ≤ Q := by
  rintro _ ⟨x, hx, rfl⟩
  exact hx.2

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ProductKernel.ProductSubspace
