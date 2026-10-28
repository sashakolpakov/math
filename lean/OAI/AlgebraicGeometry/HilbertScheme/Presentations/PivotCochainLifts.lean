import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PivotChartTorsion
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.PolynomialScalars

/-! # Pivot Cochain Lifts -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.PivotCochainLifts.ProjectiveCech

noncomputable section

/-! A finite Čech cochain admits a pivot contraction after clearing one common variable power. -/

open _root_.MvPolynomial

universe u v w

variable {σ : Type u} [LinearOrder σ]
variable (R : Type v) [CommRing R]
variable (M : Type w) [AddCommGroup M] [Module R M] [Module (MvPolynomial σ R) M]
  [IsScalarTower R (MvPolynomial σ R) M]

theorem moduleCech_pivot_local_lift (j : σ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M)
    (q : ℕ) (hf : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M q f) (s : Finset σ) :
    ∃ (k : ℕ) (y : Graded.ModuleRestriction.ProjectiveCech.ModuleChart R M s),
      (j ∈ s → y = 0) ∧ (s.card ≠ q - 1 → y = 0) ∧
      (j ∉ s → Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.subset_insert j s) y =
        X (R := R) j ^ k • (Cech.Signs.ProjectiveCech.alternatingSign R s j • f (insert j s))) := by
  by_cases hj : j ∈ s
  · exact ⟨0, 0, fun _ => rfl, fun _ => rfl, fun h => (h hj).elim⟩
  by_cases hq : s.card + 1 = q
  · obtain ⟨k, y, hy⟩ := PivotChartTorsion.ProjectiveCech.modulePivotChart_power_preimage R M j s hj (Cech.Signs.ProjectiveCech.alternatingSign R s j • f (insert j s))
    exact ⟨k, y, fun h => (hj h).elim, fun h => (h (by omega)).elim, fun _ => hy⟩
  · have hz : f (insert j s) = 0 := hf _ (by simpa only [Finset.card_insert_of_notMem hj] using hq)
    refine ⟨0, 0, fun _ => rfl, fun _ => rfl, fun _ => ?_⟩
    rw [map_zero, hz, smul_zero, smul_zero]

variable [Fintype σ]

theorem moduleCech_pivot_power_lift (j : σ) (f : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M)
    (q : ℕ) (hf : ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M q f) :
    ∃ (k : ℕ) (g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M),
      ModuleCech.Card.ProjectiveCech.ModuleCechCardSupported R M (q - 1) g ∧ (∀ s : Finset σ, j ∈ s → g s = 0) ∧
      (∀ s : Finset σ, j ∉ s → Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.subset_insert j s) (g s) =
        Cech.Signs.ProjectiveCech.alternatingSign R s j • (X (R := R) j ^ k • f (insert j s))) := by
  classical
  choose k y hz hc hy using moduleCech_pivot_local_lift R M j f q hf
  let K : ℕ := ∑ s : Finset σ, k s
  have hK (s : Finset σ) : k s ≤ K :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)
  let g : ModuleCech.Card.ProjectiveCech.ModuleCechFamily (σ := σ) R M := fun s => X (R := R) j ^ (K - k s) • y s
  refine ⟨K, g, ?_, ?_, ?_⟩
  · intro s hs
    change X (R := R) j ^ (K - k s) • y s = 0
    rw [hc s hs, smul_zero]
  · intro s hs
    change X (R := R) j ^ (K - k s) • y s = 0
    rw [hz s hs, smul_zero]
  · intro s hs
    change Graded.ModuleRestriction.ProjectiveCech.moduleChartRestriction R M (Finset.subset_insert j s) (X (R := R) j ^ (K - k s) • y s) = _
    rw [Cech.PolynomialScalars.ProjectiveCech.moduleChartRestriction_polynomial_smul, hy s hs, smul_smul, ← pow_add,
      Nat.sub_add_cancel (hK s), smul_comm]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.PivotCochainLifts.ProjectiveCech
