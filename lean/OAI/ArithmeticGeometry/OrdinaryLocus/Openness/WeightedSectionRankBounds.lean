import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.HomogeneousGeneratorImage
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FilteredModuleFiniteFrame

/-! # Weighted Section Rank Bounds -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.WeightedSectionRankBounds.Construction

noncomputable section

/-! Injective section maps with weighted polynomial images satisfy the generic-rank dimension bounds. -/

theorem weightedSection_rank_shift_bounds
    {K B σ M ι : Type*} [Field K] [CommRing B] [IsDomain B] [Algebra K B]
    [Finite σ] [Fintype ι] [AddCommGroup M] [Module K M] [Module B M]
    [IsScalarTower K B M] [Module.Flat B M] [Module.FinitePresentation B M]
    (v : σ → B) (hv : Algebra.adjoin K (Set.range v) = ⊤)
    (w : ι → M) (hw : Submodule.span B (Set.range w) = ⊤) (d : ι → ℕ)
    (E : ℕ → Type*) [∀ n, AddCommGroup (E n)] [∀ n, Module K (E n)]
    (c : ∀ n, E n →ₗ[K] M) (hc : ∀ n, Function.Injective (c n))
    (b : ℕ) (himage : ∀ n, b ≤ n → (c n).range = HomogeneousGeneratorImage.Construction.weightedPolynomialModulePiece (K := K) v w d n) :
    ∃ s : ℕ,
      (∀ n, b ≤ n → Module.rankAtStalk (R := B) M (⊥ : PrimeSpectrum B) *
        Module.finrank K (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) v n) ≤ Module.finrank K (E (n + s))) ∧
      (∀ n, b ≤ n → Module.finrank K (E n) ≤
        Module.rankAtStalk (R := B) M (⊥ : PrimeSpectrum B) *
          Module.finrank K (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) v (n + s))) := by
  let T := Submodule.span K (Set.range w)
  have hT : T.FG := Submodule.fg_span (Set.finite_range w)
  have hspan : Submodule.span B (T : Set M) = ⊤ := by
    apply top_unique
    rw [← hw]
    exact Submodule.span_mono Submodule.subset_span
  obtain ⟨a, hfinite, hlo, hhi⟩ := FilteredModuleFiniteFrame.Construction.finiteFlatModule_filtered_rank_shift_bounds v hv T hT hspan
  obtain ⟨s, hlow, hupp⟩ := HomogeneousGeneratorImage.Construction.weightedPolynomialModulePiece_comparable (K := K) v w d
  have hWfinite (n : ℕ) : Module.Finite K (HomogeneousGeneratorImage.Construction.weightedPolynomialModulePiece (K := K) v w d n) := by
    have := hfinite n
    exact Module.Finite.of_injective (Submodule.inclusion (hupp n)) (Submodule.inclusion_injective _)
  have hdim (n : ℕ) (hn : b ≤ n) :
      Module.finrank K (E n) = Module.finrank K (HomogeneousGeneratorImage.Construction.weightedPolynomialModulePiece (K := K) v w d n) := by
    rw [← himage n hn]
    exact (LinearMap.finrank_range_of_inj (hc n)).symm
  refine ⟨a + s, FilteredModuleFiniteFrame.Construction.rank_shift_bounds_of_comparable_filtrations
    (fun n => Module.finrank K (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) v n))
    (fun n => Module.finrank K (FilteredModuleFg.Construction.polynomialFilteredModule v T n))
    (fun n => Module.finrank K (E n)) _ a s b hlo hhi ?_ ?_⟩
  · intro n hn
    rw [hdim (n + s) (hn.trans (Nat.le_add_right n s))]
    have := hWfinite (n + s)
    exact Submodule.finrank_mono (hlow n)
  · intro n hn
    rw [hdim n hn]
    have := hfinite (n + s)
    exact Submodule.finrank_mono ((hupp n).trans
      (FilteredModuleFg.Construction.polynomialFilteredModule_mono v T (Nat.le_add_right n s)))

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.WeightedSectionRankBounds.Construction
