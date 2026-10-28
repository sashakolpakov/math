import OAI.Analysis.PDE.Concentration.CrudeDensity

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green

/-- The manuscript's large background parameter in physical dimension `d+1`. -/
def largeBackground (d : ℕ) (h : ℝ) : ℝ := (h ^ (30 * (d + 1)))⁻¹

theorem largeBackground_pos (d : ℕ) {h : ℝ} (hh : 0 < h) : 0 < largeBackground d h :=
  inv_pos.mpr (pow_pos hh _)

/-- The crude current bound supplies the size condition for the quadratic
output barrier, uniformly before the semiclassical scale is chosen. -/
theorem physical_density_le_largeBackground (n : ℕ) (N K C : ℝ)
    (hN : 0 ≤ N) (hK : 0 ≤ K) (hC0 : 0 ≤ C) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)) {ι : Type} [Fintype ι]
      (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
      (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3),
      0 < h → h ≤ h₀ → h ≤ a → a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ →
      (∀ j, 0 < κ j) → (Fintype.card ι : ℝ) ≤ N / h ^ (n + 2) →
      (∀ j, κ j ≤ K / h) → (∀ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ≤ C) →
      (∀ j, (∑ i, |v j i| ^ 2) ≤ 1 / 1600) →
      spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ 0 →
      (physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z x) 0 0).re ≤
        largeBackground (n + 1) h ^ (n + 1) := by
  obtain ⟨D, hD, hb⟩ := physical_packet_density_crude_bound (n + 1) N K C hN hK hC0
  have hpq : 5 * (n + 2) + 1 ≤ 30 * (n + 2) * (n + 1) := by nlinarith
  obtain ⟨h₀, hh₀, hh₀1, habs⟩ :=
    exists_crude_absorption_scale (5 * (n + 2)) (30 * (n + 2) * (n + 1)) hpq hD.le
  refine ⟨h₀, hh₀, hh₀1, ?_⟩
  intro R ι _ h a κ cR cI v z x hh hsmall hha ht hκ hcount hfreq hC hv hr
  have hbound := (hb R h a κ cR cI v z x hh (hsmall.trans hh₀1) hha ht
    hκ hcount hfreq hC hv hr).trans (habs h hh hsmall)
  simpa only [largeBackground, inv_pow, ← pow_mul, one_div, Nat.add_assoc] using hbound

end OAI.Analysis.PDE.Concentration
