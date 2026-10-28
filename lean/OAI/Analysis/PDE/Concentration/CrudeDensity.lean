import OAI.Analysis.PDE.Concentration.Lattice.Crude
import OAI.Analysis.PDE.Concentration.Packet.Fiber

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Matrix Matrix.Norms.Elementwise

theorem timeComponent_le_two_norm {d : ℕ}
    (A : Matrix (OAI.Analysis.Calculus.Current.Index d) (OAI.Analysis.Calculus.Current.Index d) (Quaternion ℝ)) : OAI.Analysis.Calculus.Current.timeComponent A ≤ 2 * ‖A‖ := by
  have hre (q : Quaternion ℝ) : |q.re| ≤ ‖q‖ := by
    have he := Quaternion.normSq_eq_norm_mul_self q
    rw [Quaternion.normSq_def'] at he
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg q.imI, sq_nonneg q.imJ, sq_nonneg q.imK, norm_nonneg q]
  have he (i j : OAI.Analysis.Calculus.Current.Index d) : |(A i j).re| ≤ ‖A‖ :=
    (hre _).trans ((norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i))
  have h00 := abs_le.mp (he none none)
  have h01 := abs_le.mp (he none (some none))
  have h10 := abs_le.mp (he (some none) none)
  have h11 := abs_le.mp (he (some none) (some none))
  simp only [OAI.Analysis.Calculus.Current.timeComponent, Quaternion.re_add, Quaternion.re_sub]
  linarith [h00.2, h01.1, h10.1, h11.2]

theorem physical_packet_density_crude_bound (d : ℕ) (N K C : ℝ)
    (hN : 0 ≤ N) (hK : 0 ≤ K) (hC0 : 0 ≤ C) :
    ∃ D : ℝ, 0 < D ∧ ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) {ι : Type} [Fintype ι]
      (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
      (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3),
      0 < h → h ≤ 1 → h ≤ a → a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ →
      (∀ j, 0 < κ j) → (Fintype.card ι : ℝ) ≤ N / h ^ (d + 1) →
      (∀ j, κ j ≤ K / h) → (∀ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ≤ C) →
      (∀ j, (∑ i, |v j i| ^ 2) ≤ 1 / 1600) →
      spatialDefiningFunction d a (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ 0 →
      (physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z x) 0 0).re ≤
        D / h ^ (5 * (d + 1)) := by
  obtain ⟨D, hD, hb⟩ := latticeRegularizedCurrent_crude_bound d N K C hN hK hC0
  refine ⟨2 * D, by positivity, ?_⟩
  intro R ι _ h a κ cR cI v z x hh hh1 hha ht hκ hcount hfreq hC hv hr
  let q := physicalToNullCurrentPoint d (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z x)
  have ha : 0 < a := hh.trans_le hha
  have hr' : OAI.Analysis.Calculus.Current.fiberDefining (1 / 10) a q.2 ≤ 0 := by
    dsimp only [q]
    rw [physicalToNullCurrentPoint_fiber_imaginary]
    exact hr
  have hay : a ≤ ‖q.2 none‖ := by
    dsimp only [q]
    rw [physicalToNullCurrentPoint_fiber_imaginary]
    exact (OAI.Analysis.Calculus.Current.fiber_collar_height_bounds a _ ha
      (by simpa only [OAI.Analysis.Calculus.Current.imaginaryTime_physicalEmbedding] using ht) (hr.trans (by norm_num))).1
  rw [physicalLatticeCurrent_time_entry]
  have hu := (timeComponent_le_two_norm _).trans
    (mul_le_mul_of_nonneg_left (hb R h a κ cR cI v q.1 q.2 hh hh1 hha hay
      hκ hcount hfreq hC hv hr') (by norm_num : (0 : ℝ) ≤ 2))
  convert hu using 1 ; ring

/-- A fixed polynomial current bound is absorbed by a larger inverse power
for all sufficiently small scales, with a threshold chosen before the scale. -/
theorem exists_crude_absorption_scale (p q : ℕ) (hpq : p + 1 ≤ q) {D : ℝ} (hD : 0 ≤ D) :
    ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ h : ℝ, 0 < h → h ≤ h₀ →
      D / h ^ p ≤ 1 / h ^ q := by
  let h₀ := min 1 (1 / (D + 1))
  have hden : 0 < D + 1 := by positivity
  refine ⟨h₀, lt_min zero_lt_one (one_div_pos.mpr hden), min_le_left _ _, ?_⟩
  intro h hh hsmall
  have hh1 : h ≤ 1 := hsmall.trans (min_le_left _ _)
  have hdh : D * h ≤ 1 := by
    have hs := (le_div_iff₀ hden).mp (hsmall.trans (min_le_right _ _))
    nlinarith
  have hp : h ^ q ≤ h ^ p * h := by
    simpa only [pow_succ] using pow_le_pow_of_le_one hh.le hh1 hpq
  apply (div_le_div_iff₀ (pow_pos hh p) (pow_pos hh q)).mpr
  calc
    D * h ^ q ≤ D * (h ^ p * h) := mul_le_mul_of_nonneg_left hp hD
    _ = (D * h) * h ^ p := by ring
    _ ≤ 1 * h ^ p := mul_le_mul_of_nonneg_right hdh (pow_nonneg hh.le _)

end OAI.Analysis.PDE.Concentration
