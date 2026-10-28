import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.IncidenceBaseChange

/-! # Generation Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.GenerationBaseChange

noncomputable section

/-! Coefficient extension preserves sums of relation modules and their images under multiplication matrices. -/

universe u v w

variable {R A : Type u} [CommRing R] [CommRing A] {ν μ : Type v}

def coordinateCoefficientLinearMap (φ : R →+* A) : (ν → R) →ₛₗ[φ] (ν → A) where
  toFun x := φ ∘ x
  map_add' x y := by ext i; exact φ.map_add _ _
  map_smul' s x := by ext i; exact φ.map_mul _ _

theorem coordinateSubmoduleExtension_gc (φ : R →+* A) :
    GaloisConnection (HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (ν := ν) φ)
      (fun K => K.comap (coordinateCoefficientLinearMap φ)) := by
  intro N K
  constructor
  · intro h x hx
    exact h (Submodule.subset_span ⟨x, hx, rfl⟩)
  · intro h
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    exact h hx

theorem coordinateSubmoduleExtension_bot (φ : R →+* A) :
    HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (ν := ν) φ ⊥ = ⊥ :=
  (coordinateSubmoduleExtension_gc φ).l_bot

theorem coordinateSubmoduleExtension_iSup {ι : Sort w} (φ : R →+* A)
    (N : ι → Submodule R (ν → R)) :
    HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension φ (⨆ i, N i) = ⨆ i, HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension φ (N i) :=
  (coordinateSubmoduleExtension_gc φ).l_iSup

theorem coordinateSubmoduleExtension_linearImage [Fintype ν] [DecidableEq ν]
    (φ : R →+* A) (N : Submodule R (ν → R)) (F : Matrix μ ν R) :
    HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension φ (N.map (Matrix.toLin' F)) =
      (HilbertScheme.Presentations.Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension φ N).map (Matrix.toLin' (F.map φ)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨φ ∘ x, Submodule.subset_span ⟨x, hx, rfl⟩, ?_⟩
    ext i
    exact (RingHom.map_mulVec φ F x i).symm
  · change (Submodule.span A _).map (Matrix.toLin' (F.map φ)) ≤ _
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    have he : Matrix.toLin' (F.map φ) (φ ∘ x) = φ ∘ Matrix.toLin' F x := by
      ext i
      exact (RingHom.map_mulVec φ F x i).symm
    rw [he]
    exact Submodule.subset_span ⟨Matrix.toLin' F x, ⟨x, hx, rfl⟩, rfl⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.GenerationBaseChange
