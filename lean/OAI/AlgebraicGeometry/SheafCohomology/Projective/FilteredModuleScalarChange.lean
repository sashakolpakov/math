import OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredModuleFg

/-! # Filtered Module Scalar Change -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredModuleScalarChange.Dimension

noncomputable section

/-! Polynomial module filtrations agree after factoring their scalar action through an algebra map. -/

open _root_.MvPolynomial

theorem polynomialFilteredModule_change_scalars
    {K A B σ M : Type*} [Field K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module A M] [Module B M]
    [IsScalarTower K A M] [IsScalarTower K B M]
    (φ : A →ₐ[K] B) (hφ : ∀ (a : A) (x : M), a • x = φ a • x)
    (v : σ → A) (T : Submodule K M) (n : ℕ) :
    FilteredModuleFg.Dimension.polynomialFilteredModule v T n = FilteredModuleFg.Dimension.polynomialFilteredModule (fun i => φ (v i)) T n := by
  apply le_antisymm
  · apply Submodule.smul_le.mpr
    intro a ha x hx
    rw [hφ]
    obtain ⟨p, hp, rfl⟩ := (PolynomialFilteredAlgebra.Dimension.mem_polynomialFilteredPiece v n a).mp ha
    apply Submodule.smul_mem_smul _ hx
    exact (PolynomialFilteredAlgebra.Dimension.mem_polynomialFilteredPiece (fun i => φ (v i)) n _).mpr
      ⟨p, hp, (MvPolynomial.comp_aeval_apply v φ p).symm⟩
  · apply Submodule.smul_le.mpr
    intro b hb x hx
    obtain ⟨p, hp, rfl⟩ := (PolynomialFilteredAlgebra.Dimension.mem_polynomialFilteredPiece (fun i => φ (v i)) n b).mp hb
    rw [← MvPolynomial.comp_aeval_apply v φ p, ← hφ]
    exact Submodule.smul_mem_smul ((PolynomialFilteredAlgebra.Dimension.mem_polynomialFilteredPiece v n _).mpr ⟨p, hp, rfl⟩) hx

theorem span_eq_top_of_factored_scalars
    {A B M : Type*} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M] [Module B M]
    (φ : A →+* B) (hφ : ∀ (a : A) (x : M), a • x = φ a • x)
    (s : Set M) (hs : Submodule.span A s = ⊤) : Submodule.span B s = ⊤ := by
  apply top_unique
  intro x hxTop
  clear hxTop
  have hx : x ∈ Submodule.span A s := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [hφ]
    exact Submodule.smul_mem _ (φ a) hx

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FilteredModuleScalarChange.Dimension
