import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.KernelDimensionCriterion

/-! # Kernel Exact Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.KernelExactCriterion

noncomputable section

/-! Bijectivity of the specified cycle comparison is equivalent to
injectivity and exactness, over an arbitrary coefficient ring. -/
universe u v w z
variable {R : Type u} [CommRing R]
variable {V : Type v} [AddCommGroup V] [Module R V]
variable {M : Type w} [AddCommGroup M] [Module R M]
variable {N : Type z} [AddCommGroup N] [Module R N]

theorem linearKernelComparison_injective_iff
    (s : V →ₗ[R] M) (d : M →ₗ[R] N) (h : d.comp s = 0) :
    Function.Injective (KernelDimensionCriterion.linearKernelComparison s d h) ↔ Function.Injective s := by
  constructor
  · intro hs x y hxy
    exact hs (Subtype.ext hxy)
  · intro hs x y hxy
    exact hs (congrArg Subtype.val hxy)

theorem linearKernelComparison_surjective_iff_range
    (s : V →ₗ[R] M) (d : M →ₗ[R] N) (h : d.comp s = 0) :
    Function.Surjective (KernelDimensionCriterion.linearKernelComparison s d h) ↔ s.range = d.ker := by
  constructor
  · intro hs
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact LinearMap.congr_fun h x
    · intro x hx
      obtain ⟨y, hy⟩ := hs ⟨x, hx⟩
      exact ⟨y, congrArg Subtype.val hy⟩
  · intro hs x
    have hx : x.val ∈ s.range := hs.symm ▸ x.property
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, Subtype.ext hy⟩

theorem linearKernelComparison_bijective_iff_exact
    (s : V →ₗ[R] M) (d : M →ₗ[R] N) (h : d.comp s = 0) :
    Function.Bijective (KernelDimensionCriterion.linearKernelComparison s d h) ↔
      Function.Injective s ∧ s.range = d.ker := by
  exact and_congr (linearKernelComparison_injective_iff s d h)
    (linearKernelComparison_surjective_iff_range s d h)

theorem linearKernelComparison_bijective_iff_values
    (s : V →ₗ[R] M) (d : M →ₗ[R] N) (h : d.comp s = 0) :
    Function.Bijective (KernelDimensionCriterion.linearKernelComparison s d h) ↔
      Function.Injective s ∧ ∀ x, d x = 0 → ∃ y, s y = x := by
  constructor
  · intro hs
    refine ⟨(linearKernelComparison_injective_iff s d h).mp hs.injective, ?_⟩
    intro x hx
    obtain ⟨y, hy⟩ := hs.surjective ⟨x, hx⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨hi, he⟩
    refine ⟨(linearKernelComparison_injective_iff s d h).mpr hi, ?_⟩
    intro x
    obtain ⟨y, hy⟩ := he x.val x.property
    exact ⟨y, Subtype.ext hy⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.KernelExactCriterion
