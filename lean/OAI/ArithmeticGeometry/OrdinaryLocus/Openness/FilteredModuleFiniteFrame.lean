import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FilteredModuleFg
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FilteredModuleMaps
import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FiniteModuleSandwich

/-! # Filtered Module Finite Frame -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FilteredModuleFiniteFrame.Construction

noncomputable section

section

/-! Generic-rank injections give the two shifted dimension bounds for finite-module filtrations. -/

variable {K B σ M : Type*} [Field K] [CommRing B] [Algebra K B] [Finite σ]
    [AddCommGroup M] [Module K M] [Module B M] [IsScalarTower K B M]

theorem polynomialFilteredModule_rank_shift_bounds
    (v : σ → B) (hv : Algebra.adjoin K (Set.range v) = ⊤)
    (T : Submodule K M) (hT : T.FG) (hspan : Submodule.span B (T : Set M) = ⊤)
    (d : ℕ) (i : M →ₗ[B] (Fin d → B)) (j : (Fin d → B) →ₗ[B] M)
    (hi : Function.Injective i) (hj : Function.Injective j) :
    ∃ c : ℕ, (∀ n : ℕ, Module.Finite K (FilteredModuleFg.Construction.polynomialFilteredModule v T n)) ∧
      (∀ n : ℕ, d * Module.finrank K (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) v n) ≤
        Module.finrank K (FilteredModuleFg.Construction.polynomialFilteredModule v T (n + c))) ∧
      (∀ n : ℕ, Module.finrank K (FilteredModuleFg.Construction.polynomialFilteredModule v T n) ≤
        d * Module.finrank K (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) v (n + c))) := by
  let S : Submodule K (Fin d → B) := FilteredModuleFg.Construction.finiteFreeConstantFrame
  obtain ⟨a, ha⟩ := FilteredModuleMaps.Construction.exists_polynomialFilteredModule_map_shift v hv T hT S
    FilteredModuleFg.Construction.finiteFreeConstantFrame_scalarSpan i
  obtain ⟨b, hb⟩ := FilteredModuleMaps.Construction.exists_polynomialFilteredModule_map_shift v hv S FilteredModuleFg.Construction.finiteFreeConstantFrame_fg T hspan j
  let c := max a b
  have hu (n : ℕ) : (FilteredModuleFg.Construction.polynomialFilteredModule v T n).map (i.restrictScalars K) ≤
      FilteredModuleFg.Construction.polynomialFilteredModule v S (n + c) :=
    (ha n).trans (FilteredModuleFg.Construction.polynomialFilteredModule_mono v S (Nat.add_le_add_left (le_max_left a b) n))
  have hl (n : ℕ) : (FilteredModuleFg.Construction.polynomialFilteredModule v S n).map (j.restrictScalars K) ≤
      FilteredModuleFg.Construction.polynomialFilteredModule v T (n + c) :=
    (hb n).trans (FilteredModuleFg.Construction.polynomialFilteredModule_mono v T (Nat.add_le_add_left (le_max_right a b) n))
  have hfinite (n : ℕ) : Module.Finite K (FilteredModuleFg.Construction.polynomialFilteredModule v T n) :=
    Module.Finite.of_injective (FilteredModuleMaps.Construction.filteredModuleMap v T S i n (n + c) (hu n))
      (FilteredModuleMaps.Construction.filteredModuleMap_injective v T S i hi n (n + c) (hu n))
  refine ⟨c, hfinite, ?_, ?_⟩
  · intro n
    have := hfinite (n + c)
    have h := FilteredModuleMaps.Construction.filteredModuleMap_finrank_le v S T j hj n (n + c) (hl n)
    simpa only [S, FilteredModuleFg.Construction.polynomialFilteredFree_finrank, Fintype.card_fin] using h
  · intro n
    have h := FilteredModuleMaps.Construction.filteredModuleMap_finrank_le v T S i hi n (n + c) (hu n)
    simpa only [S, FilteredModuleFg.Construction.polynomialFilteredFree_finrank, Fintype.card_fin] using h

theorem finiteFlatModule_filtered_rank_shift_bounds [IsDomain B]
    [Module.Flat B M] [Module.FinitePresentation B M]
    (v : σ → B) (hv : Algebra.adjoin K (Set.range v) = ⊤)
    (T : Submodule K M) (hT : T.FG) (hspan : Submodule.span B (T : Set M) = ⊤) :
    ∃ c : ℕ, (∀ n : ℕ, Module.Finite K (FilteredModuleFg.Construction.polynomialFilteredModule v T n)) ∧
      (∀ n : ℕ, Module.rankAtStalk (R := B) M (⊥ : PrimeSpectrum B) *
        Module.finrank K (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) v n) ≤
          Module.finrank K (FilteredModuleFg.Construction.polynomialFilteredModule v T (n + c))) ∧
      (∀ n : ℕ, Module.finrank K (FilteredModuleFg.Construction.polynomialFilteredModule v T n) ≤
        Module.rankAtStalk (R := B) M (⊥ : PrimeSpectrum B) *
          Module.finrank K (PolynomialFilteredAlgebra.Construction.polynomialFilteredPiece (K := K) v (n + c))) := by
  let d := Module.rankAtStalk (R := B) M (⊥ : PrimeSpectrum B)
  obtain ⟨i, j, hi, hj⟩ := FiniteModuleSandwich.Construction.finiteFlatModule_rankAtStalk_injections B M
  let e := Finsupp.linearEquivFunOnFinite B B (Fin d)
  exact polynomialFilteredModule_rank_shift_bounds v hv T hT hspan d
    (e.toLinearMap.comp i) (j.comp e.symm.toLinearMap)
    (e.injective.comp hi) (hj.comp e.symm.injective)

end

/-! A finite module has a finite base-field subspace generating its exhaustive degree filtration. -/

theorem finiteModule_exists_finite_frame
    (K B M : Type*) [Field K] [CommRing B] [Algebra K B]
    [AddCommGroup M] [Module K M] [Module B M] [IsScalarTower K B M] [Module.Finite B M] :
    ∃ T : Submodule K M, T.FG ∧ Submodule.span B (T : Set M) = ⊤ := by
  obtain ⟨d, w, hw⟩ := Module.Finite.exists_fin (R := B) (M := M)
  refine ⟨Submodule.span K (Set.range w), Submodule.fg_span (Set.finite_range w), ?_⟩
  apply top_unique
  rw [← hw]
  exact Submodule.span_mono Submodule.subset_span

theorem rank_shift_bounds_of_comparable_filtrations
    (P F H : ℕ → ℕ) (d a b c : ℕ)
    (hlo : ∀ n, d * P n ≤ F (n + a))
    (hhi : ∀ n, F n ≤ d * P (n + a))
    (hFH : ∀ n, c ≤ n → F n ≤ H (n + b))
    (hHF : ∀ n, c ≤ n → H n ≤ F (n + b)) :
    (∀ n, c ≤ n → d * P n ≤ H (n + (a + b))) ∧
      (∀ n, c ≤ n → H n ≤ d * P (n + (a + b))) := by
  constructor
  · intro n hn
    simpa only [Nat.add_assoc] using
      (hlo n).trans (hFH (n + a) (hn.trans (Nat.le_add_right n a)))
  · intro n hn
    have h := (hHF n hn).trans (hhi (n + b))
    simpa only [Nat.add_assoc, Nat.add_comm b a] using h

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.FilteredModuleFiniteFrame.Construction
