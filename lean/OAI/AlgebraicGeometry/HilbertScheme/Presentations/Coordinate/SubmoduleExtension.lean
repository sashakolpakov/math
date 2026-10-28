import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.KernelBaseChange

/-! # Submodule Extension -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.SubmoduleExtension.Grassmannian

noncomputable section

/-! Functoriality of extension of coordinate relations and compatibility of local quotient matrices. -/

universe u v w

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] {ν : Type w}

theorem coordinateSubmoduleExtension_id (N : Submodule R (ν → R)) :
    Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (RingHom.id R) N = N := by
  change Submodule.span R (id '' (N : Set (ν → R))) = N
  rw [Set.image_id, Submodule.span_eq]

theorem coordinateSubmoduleExtension_comp (φ : R →+* S) (ψ : S →+* T)
    (N : Submodule R (ν → R)) :
    Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (ψ.comp φ) N =
      Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension ψ (Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension φ N) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    apply Submodule.subset_span
    exact ⟨φ ∘ x, Submodule.subset_span ⟨x, hx, rfl⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨y, hy, rfl⟩
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, hx, rfl⟩ := hy
      exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have hz : ψ ∘ (0 : ν → S) = 0 := by ext i; exact ψ.map_zero
      change ψ ∘ (0 : ν → S) ∈ Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (ψ.comp φ) N
      rw [hz]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have he : ψ ∘ (x + y) = ψ ∘ x + ψ ∘ y := by ext i; exact ψ.map_add _ _
      change ψ ∘ (x + y) ∈ Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (ψ.comp φ) N
      rw [he]
      exact Submodule.add_mem _ hx hy
    | smul s x _ hx =>
      have he : ψ ∘ (s • x) = ψ s • (ψ ∘ x) := by ext i; exact ψ.map_mul _ _
      change ψ ∘ (s • x) ∈ Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (ψ.comp φ) N
      rw [he]
      exact Submodule.smul_mem _ _ hx

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

theorem coordinateSubmoduleExtension_injective (e : R ≃+* S) :
    Function.Injective (Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension (ν := ν) e.toRingHom) := by
  intro N M h
  have h' := congrArg (Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension e.symm.toRingHom) h
  rw [← coordinateSubmoduleExtension_comp, ← coordinateSubmoduleExtension_comp] at h'
  have he : e.symm.toRingHom.comp e.toRingHom = RingHom.id R := by
    ext r
    exact e.symm_apply_apply r
  rw [he, coordinateSubmoduleExtension_id, coordinateSubmoduleExtension_id] at h'
  exact h'

variable {ι : Type v} [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

theorem normalizedLocalQuotients_kernel_eq
    (α : R →+* A) (β : R →+* B) (φ : A →+* C) (ψ : B →+* C)
    (hφ : φ.comp α = ψ.comp β) (N : Submodule R (ν → R))
    (a b : ι → ν) (Q : Matrix ι ν A) (K : Matrix ι ν B)
    (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q) (hK : Normalized.Matrices.Grassmannian.IsNormalized b K)
    (hQN : (Matrix.toLin' Q).ker = Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension α N)
    (hKN : (Matrix.toLin' K).ker = Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension β N) :
    (Matrix.toLin' (Q.map φ)).ker = (Matrix.toLin' (K.map ψ)).ker := by
  rw [← Normalized.KernelBaseChange.Grassmannian.normalizedKernel_baseChange φ a Q hQ, ← Normalized.KernelBaseChange.Grassmannian.normalizedKernel_baseChange ψ b K hK,
    hQN, hKN, ← coordinateSubmoduleExtension_comp, ← coordinateSubmoduleExtension_comp, hφ]

theorem normalizedLocalQuotients_transition
    (α : R →+* A) (β : R →+* B) (φ : A →+* C) (ψ : B →+* C)
    (hφ : φ.comp α = ψ.comp β) (N : Submodule R (ν → R))
    (a b : ι → ν) (Q : Matrix ι ν A) (K : Matrix ι ν B)
    (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q) (hK : Normalized.Matrices.Grassmannian.IsNormalized b K)
    (hQN : (Matrix.toLin' Q).ker = Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension α N)
    (hKN : (Matrix.toLin' K).ker = Normalized.KernelBaseChange.Grassmannian.coordinateSubmoduleExtension β N) :
    IsUnit (Normalized.Matrices.Grassmannian.selectedColumns b (Q.map φ)).det ∧ K.map ψ = Normalized.Matrices.Grassmannian.normalizeColumns b (Q.map φ) :=
  (Normalized.OverlapEquations.Grassmannian.quotientCompatibility_iff_transition a b _ _ (hQ.map φ)).mp
    ((Normalized.OverlapEquations.Grassmannian.quotientCompatibility_iff_kernel_eq a b _ _ (hQ.map φ) (hK.map ψ)).mpr
      (normalizedLocalQuotients_kernel_eq α β φ ψ hφ N a b Q K hQ hK hQN hKN))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.SubmoduleExtension.Grassmannian
