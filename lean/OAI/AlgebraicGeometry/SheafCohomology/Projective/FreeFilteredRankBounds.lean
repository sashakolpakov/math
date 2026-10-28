import OAI.AlgebraicGeometry.SheafCohomology.Projective.FiniteTorsionFreeSandwich
import OAI.AlgebraicGeometry.SheafCohomology.Projective.WeightedSectionRankBounds

/-! # Free Filtered Rank Bounds -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.FreeFilteredRankBounds.Dimension

noncomputable section

/-! Torsion-free generic rank controls the leading growth of actual filtered section spaces. -/

open scoped TensorProduct

theorem finiteTorsionFreeModule_filtered_rank_shift_bounds
    {K B σ M : Type*} [Field K] [CommRing B] [IsDomain B] [Algebra K B] [Finite σ]
    [AddCommGroup M] [Module K M] [Module B M] [IsScalarTower K B M]
    [Module.IsTorsionFree B M] [Module.FinitePresentation B M]
    (F : Type*) [Field F] [Algebra B F] [IsFractionRing B F]
    (v : σ → B) (hv : Algebra.adjoin K (Set.range v) = ⊤)
    (T : Submodule K M) (hT : T.FG) (hspan : Submodule.span B (T : Set M) = ⊤) :
    let d := Module.finrank F (F ⊗[B] M)
    ∃ c : ℕ, (∀ n : ℕ, Module.Finite K (FilteredModuleFg.Dimension.polynomialFilteredModule v T n)) ∧
      (∀ n : ℕ, d * Module.finrank K (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n) ≤
        Module.finrank K (FilteredModuleFg.Dimension.polynomialFilteredModule v T (n + c))) ∧
      (∀ n : ℕ, Module.finrank K (FilteredModuleFg.Dimension.polynomialFilteredModule v T n) ≤
        d * Module.finrank K (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v (n + c))) := by
  let d := Module.finrank F (F ⊗[B] M)
  obtain ⟨i, j, hi, hj⟩ := FiniteTorsionFreeSandwich.Dimension.finiteTorsionFreeModule_genericRank_injections B F M
  let e := Finsupp.linearEquivFunOnFinite B B (Fin d)
  exact FilteredModuleFiniteFrame.Dimension.polynomialFilteredModule_rank_shift_bounds v hv T hT hspan d
    (e.toLinearMap.comp i) (j.comp e.symm.toLinearMap)
    (e.injective.comp hi) (hj.comp e.symm.injective)

theorem weightedTorsionFreeSection_rank_shift_bounds
    {K B σ M ι : Type*} [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [Finite σ] [Fintype ι] [AddCommGroup M] [Module K M] [Module B M]
    [IsScalarTower K B M] [Module.IsTorsionFree B M] [Module.FinitePresentation B M]
    (F : Type*) [Field F] [Algebra B F] [IsFractionRing B F]
    (v : σ → B) (hv : Algebra.adjoin K (Set.range v) = ⊤)
    (w : ι → M) (hw : Submodule.span B (Set.range w) = ⊤) (d : ι → ℕ)
    (E : ℕ → Type*) [∀ n, AddCommGroup (E n)] [∀ n, Module K (E n)]
    (c : ∀ n, E n →ₗ[K] M) (hc : ∀ n, Function.Injective (c n))
    (b : ℕ) (himage : ∀ n, b ≤ n → (c n).range = HomogeneousGeneratorImage.Dimension.weightedPolynomialModulePiece (K := K) v w d n) :
    let rank := Module.finrank F (F ⊗[B] M)
    ∃ s : ℕ,
      (∀ n, b ≤ n → rank * Module.finrank K (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n) ≤
        Module.finrank K (E (n + s))) ∧
      (∀ n, b ≤ n → Module.finrank K (E n) ≤
        rank * Module.finrank K (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v (n + s))) := by
  let T := Submodule.span K (Set.range w)
  have hT : T.FG := Submodule.fg_span (Set.finite_range w)
  have hspan : Submodule.span B (T : Set M) = ⊤ := by
    apply top_unique
    rw [← hw]
    exact Submodule.span_mono Submodule.subset_span
  obtain ⟨a, hfinite, hlo, hhi⟩ := finiteTorsionFreeModule_filtered_rank_shift_bounds F v hv T hT hspan
  obtain ⟨s, hlow, hupp⟩ := HomogeneousGeneratorImage.Dimension.weightedPolynomialModulePiece_comparable (K := K) v w d
  have hWfinite (n : ℕ) : Module.Finite K (HomogeneousGeneratorImage.Dimension.weightedPolynomialModulePiece (K := K) v w d n) := by
    have := hfinite n
    exact Module.Finite.of_injective (Submodule.inclusion (hupp n)) (Submodule.inclusion_injective _)
  have hdim (n : ℕ) (hn : b ≤ n) :
      Module.finrank K (E n) = Module.finrank K (HomogeneousGeneratorImage.Dimension.weightedPolynomialModulePiece (K := K) v w d n) := by
    rw [← himage n hn]
    exact (LinearMap.finrank_range_of_inj (hc n)).symm
  refine ⟨a + s, FilteredModuleFiniteFrame.Dimension.rank_shift_bounds_of_comparable_filtrations
    (fun n => Module.finrank K (PolynomialFilteredAlgebra.Dimension.polynomialFilteredPiece (K := K) v n))
    (fun n => Module.finrank K (FilteredModuleFg.Dimension.polynomialFilteredModule v T n))
    (fun n => Module.finrank K (E n)) _ a s b hlo hhi ?_ ?_⟩
  · intro n hn
    rw [hdim (n + s) (hn.trans (Nat.le_add_right n s))]
    have := hWfinite (n + s)
    exact Submodule.finrank_mono (hlow n)
  · intro n hn
    rw [hdim n hn]
    have := hfinite (n + s)
    exact Submodule.finrank_mono ((hupp n).trans
      (FilteredModuleFg.Dimension.polynomialFilteredModule_mono v T (Nat.le_add_right n s)))

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.FreeFilteredRankBounds.Dimension
