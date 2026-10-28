import OAI.NumberTheory.PadicHodge.GeometricComparison.Linear

/-! # Filtered Image Dimension -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FilteredImageDimension.FiltrationTransport

noncomputable section

/-! Rank-nullity bounds an actual filtration step by its kernel and its image. -/

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

def kernelDomRestrictEquiv (f : V →ₗ[K] W) (P : Submodule K V) :
    (f.domRestrict P).ker ≃ₗ[K] (f.ker ⊓ P : Submodule K V) where
  toFun x := ⟨x.1.1, x.2, x.1.2⟩
  invFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem filtered_image_dimension [FiniteDimensional K V] [FiniteDimensional K W]
    (f : V →ₗ[K] W) (P : Submodule K V) (Q : Submodule K W) (h : P.map f ≤ Q) :
    Module.finrank K P ≤ Module.finrank K (f.ker ⊓ P : Submodule K V) +
      Module.finrank K (f.range ⊓ Q : Submodule K W) := by
  have hr : (f.domRestrict P).range ≤ f.range ⊓ Q := by
    rintro y ⟨x, rfl⟩
    exact ⟨⟨x, rfl⟩, h ⟨x, x.property, rfl⟩⟩
  have hdim := Submodule.finrank_mono hr
  have hnull := (f.domRestrict P).finrank_range_add_finrank_ker
  rw [(kernelDomRestrictEquiv f P).finrank_eq] at hnull
  omega

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FilteredImageDimension.FiltrationTransport
