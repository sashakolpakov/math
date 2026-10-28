import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualDegreeFlatness

/-! # Eventual Irrelevant Torsion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualIrrelevantTorsion.ProjectiveCech

noncomputable section

/-! Irrelevant torsion in a finite graded polynomial module vanishes in all sufficiently high degrees. -/

open _root_.MvPolynomial DirectSum

universe u v

variable {σ : Type v} [Fintype σ] [LinearOrder σ]
variable (R : Type u) [CommRing R]
variable (M : Type (max u v)) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

def moduleAugmentationCochain (m : M) : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M :=
  fun s => if s.card = 0 then Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) 0 m else 0

omit [Fintype σ] [LinearOrder σ] in
theorem moduleAugmentationCochain_card (m : M) :
    ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M 0 (moduleAugmentationCochain (σ := σ) R M m) := by
  intro s hs
  simp only [moduleAugmentationCochain, ite_eq_right hs]

omit [Fintype σ] [LinearOrder σ] in
theorem moduleAugmentationCochain_homogeneous (ℳ : ℤ → Submodule R M)
    (d : ℤ) (m : M) (hm : m ∈ ℳ d) :
    ModuleCech.Card.ProjectiveCech.ModuleCechHomogeneous R M ℳ d (moduleAugmentationCochain (σ := σ) R M m) := by
  intro s
  by_cases hs : s.card = 0
  · simp only [moduleAugmentationCochain, ite_eq_left hs]
    apply Localized.DegreePieces.GradedModules.moduleFractionMap_mem_degree ℳ _ _ d 0 m
    simpa only [Nat.cast_zero, zero_mul, add_zero] using hm
  · simpa only [moduleAugmentationCochain, ite_eq_right hs] using
      (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R M ℳ s d).zero_mem

omit [Fintype σ] in
theorem chartFraction_zero_of_variable_torsion (m : M)
    (hm : ∀ i : σ, ∃ k : ℕ, X (R := R) i ^ k • m = 0)
    (s : Finset σ) (hs : s.Nonempty) :
    Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) 0 m = 0 := by
  obtain ⟨i, hi⟩ := hs
  obtain ⟨k, hk⟩ := hm i
  apply (Presentations.Module.Fractions.GradedModules.moduleFractionMap_eq_zero (R := R) _ 0 m).mpr
  refine ⟨k, ?_⟩
  rw [EventualDegreeFlatness.ProjectiveCech.inversionMonomial_factor_variable R s i hi, mul_pow, mul_comm, mul_smul, hk, smul_zero]

omit [Fintype σ] in
theorem moduleAugmentationCochain_cycle_of_variable_torsion (m : M)
    (hm : ∀ i : σ, ∃ k : ℕ, X (R := R) i ^ k • m = 0) :
    ModuleCech.Card.ProjectiveCech.moduleCechDifferential R M (moduleAugmentationCochain (σ := σ) R M m) = 0 := by
  funext s
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hsi : (s.erase i).card = 0
  · simp only [moduleAugmentationCochain, ite_eq_left hsi, Presentations.Module.ChartCompatibility.ProjectiveCech.moduleChartRestriction_fraction,
      pow_zero, one_smul, chartFraction_zero_of_variable_torsion R M m hm s ⟨i, hi⟩, smul_zero]
  · simp only [moduleAugmentationCochain, ite_eq_right hsi, map_zero, smul_zero]

theorem eventual_no_irrelevant_torsion [Nonempty σ] [IsNoetherianRing R]
    (ℳ : ℤ → Submodule R M) [Decomposition ℳ]
    [SetLike.GradedSMul (WeightedFreeModules.GradedModules.polynomialIntegerGrading (σ := σ) R) ℳ]
    [Module.Finite (MvPolynomial σ R) M] :
    ∃ N : ℕ, ∀ d : ℤ, (N : ℤ) ≤ d → ∀ m : M, m ∈ ℳ d →
      (∀ i : σ, ∃ k : ℕ, X (R := R) i ^ k • m = 0) → m = 0 := by
  obtain ⟨N, hN⟩ := Graded.CechVanishing.ProjectiveCech.moduleCech_eventual_exactness_explicit (σ := σ) R M ℳ
  refine ⟨N, fun d hd m hm ht => ?_⟩
  have hz := (hN d hd).1 (moduleAugmentationCochain (σ := σ) R M m)
    (moduleAugmentationCochain_homogeneous R M ℳ d m hm)
    (moduleAugmentationCochain_card R M m)
    (moduleAugmentationCochain_cycle_of_variable_torsion R M m ht)
  apply (Cech.AugmentationDegree.ProjectiveCech.emptyModuleChartEquiv (σ := σ) R M).injective
  change Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial (σ := σ) R ∅) 0 m =
    Presentations.Module.Fractions.GradedModules.moduleFractionMap (R := R) (LaurentMonomials.ProjectiveCech.inversionMonomial (σ := σ) R ∅) 0 0
  have he := congrFun hz ∅
  simpa only [moduleAugmentationCochain, Finset.card_empty, ite_eq_left rfl, ite_true,
    Pi.zero_apply, map_zero] using he

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualIrrelevantTorsion.ProjectiveCech
