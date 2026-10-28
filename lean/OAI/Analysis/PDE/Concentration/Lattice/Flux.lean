import OAI.Analysis.PDE.Concentration.Physical.LatticeCurrent

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Matrix Matrix.Norms.Elementwise

def latticeWavePart {d : ℕ} {ι : Type*} [Fintype ι]
    (L : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) : Matrix (OAI.Analysis.Calculus.Current.Index d) (OAI.Analysis.Calculus.Current.Index d) (Quaternion ℝ) :=
  OAI.Analysis.Calculus.Current.cutoffCurrent OAI.Analysis.Calculus.Current.phaseCutoff a
    (OAI.Analysis.Calculus.Current.averagedWaveCurrent (latticeKernelMeasure L h) (latticeCubeShift L) κ cR cI v) x z

theorem latticeWavePart_lateral_norm_le {d : ℕ} {ι : Type*} [Fintype ι]
    (L : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a R C k : ℝ) (hh : 0 < h) (hR0 : 0 ≤ R) (hC0 : 0 ≤ C)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (hκ : ∀ j, 0 < κ j) (hk : ∀ j, k ≤ κ j)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) (hY : z none ≠ 0)
    (hR : ∀ j, κ j / ‖z none‖ ≤ R) (hC : ∀ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ≤ C)
    (hv : ∀ j, (∑ i, |v j i| ^ 2) ≤ 1 / 1600)
    (hr : OAI.Analysis.Calculus.Current.fiberDefining (1 / 10) a z = 0) :
    ‖latticeWavePart L h a κ cR cI v x z‖ ≤ ((Fintype.card ι : ℝ) * ((d : ℝ) + 1) *
      (R ^ ((d : ℝ) / 2) * Real.exp (-(k * ‖z none‖ / 3200)) * C)) ^ 2 := by
  by_cases hg : OAI.Analysis.Calculus.Current.phaseCutoff (OAI.Analysis.Calculus.Current.phi z / (a : ℂ)) = 0
  · simp only [latticeWavePart, OAI.Analysis.Calculus.Current.cutoffCurrent, hg, zero_smul, norm_zero]
    positivity
  let := latticeKernelMeasure_isProbability L h hh
  apply (OAI.Analysis.Calculus.Current.cutoffCurrent_norm_le a _ x z).trans
  have hn := norm_integral_le_of_norm_le_const (μ := latticeKernelMeasure L h)
    (Filter.Eventually.of_forall fun t => OAI.Analysis.Calculus.Current.waveCurrent_lateral_norm_le a R C k hR0 hC0
      κ cR cI v hκ hk (x + latticeCubeShift L t) z hY hR hC hv hr hg)
  simpa [OAI.Analysis.Calculus.Current.averagedWaveCurrent, measureReal_def] using! hn

theorem latticeWavePart_lateral_power_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (L : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a R C k b M : ℝ) (hh : 0 < h) (hR0 : 0 ≤ R) (hC0 : 0 ≤ C)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (hκ : ∀ j, 0 < κ j) (hk : ∀ j, k ≤ κ j)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) (hY : z none ≠ 0)
    (hR : ∀ j, κ j / ‖z none‖ ≤ R) (hC : ∀ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ≤ C)
    (hv : ∀ j, (∑ i, |v j i| ^ 2) ≤ 1 / 1600)
    (hr : OAI.Analysis.Calculus.Current.fiberDefining (1 / 10) a z = 0)
    (hpoly : (Fintype.card ι : ℝ) * ((d : ℝ) + 1) *
      (R ^ ((d : ℝ) / 2) * C) ≤ h ^ (-b))
    (hlog : (b + M / 2) * Real.log h⁻¹ ≤ k * ‖z none‖ / 3200) :
    ‖latticeWavePart L h a κ cR cI v x z‖ ≤ h ^ M := by
  have he := OAI.Analysis.Calculus.Current.exp_neg_le_rpow_of_log_bound h (b + M / 2) _ hh hlog
  have hnonneg : 0 ≤ (Fintype.card ι : ℝ) * ((d : ℝ) + 1) *
      (R ^ ((d : ℝ) / 2) * C) := by positivity
  have hp := mul_le_mul hpoly he (Real.exp_nonneg _) (Real.rpow_nonneg hh.le _)
  have hpow : h ^ (-b) * h ^ (b + M / 2) = h ^ (M / 2) := by
    rw [← Real.rpow_add hh]
    congr 1
    ring
  rw [hpow] at hp
  have hsq := pow_le_pow_left₀ (mul_nonneg hnonneg (Real.exp_nonneg _)) hp 2
  have hsqpow : (h ^ (M / 2)) ^ 2 = h ^ M := by
    rw [pow_two, ← Real.rpow_add hh]
    congr 1
    ring
  rw [hsqpow] at hsq
  refine (latticeWavePart_lateral_norm_le L h a R C k hh hR0 hC0
    κ cR cI v hκ hk x z hY hR hC hv hr).trans ?_
  convert hsq using 1 ; ring

theorem latticeRegularizedCurrent_normal_flux_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (L : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (z : OAI.Analysis.Calculus.Current.Index d → ℂ) (hY : z none ≠ 0) :
    ‖star (OAI.Analysis.Calculus.Current.fiberGradient (1 / 10) a z) ᵥ* latticeRegularizedCurrent L h a κ cR cI v x z‖ ≤
      ((d : ℝ) + 2) * ‖OAI.Analysis.Calculus.Current.fiberGradient (1 / 10) a z‖ * ‖latticeWavePart L h a κ cR cI v x z‖ := by
  have he : star (OAI.Analysis.Calculus.Current.fiberGradient (1 / 10) a z) ᵥ* latticeRegularizedCurrent L h a κ cR cI v x z =
      star (OAI.Analysis.Calculus.Current.fiberGradient (1 / 10) a z) ᵥ* latticeWavePart L h a κ cR cI v x z := by
    change _ ᵥ* (latticeWavePart L h a κ cR cI v x z +
      h ^ (50 * (d + 1)) • OAI.Analysis.Calculus.Current.fiberCofactor (1 / 10) a z) = _
    rw [Matrix.vecMul_add, Matrix.vecMul_smul, OAI.Analysis.Calculus.Current.fiberCofactor_normal_row_zero _ _ _ hY,
      smul_zero, add_zero]
  rw [he]
  simpa [OAI.Analysis.Calculus.Current.Index, norm_star, add_assoc] using OAI.Analysis.Calculus.Current.quaternion_vecMul_norm_le
    (star (OAI.Analysis.Calculus.Current.fiberGradient (1 / 10) a z)) (latticeWavePart L h a κ cR cI v x z)

/-- The boundary error constant is independent of the spatial lattice chart. -/
theorem physicalLatticeCurrent_lateral_power_flux_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (L : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (h a R C k b M : ℝ) (hh : 0 < h) (hha : h ≤ a)
    (hR0 : 0 ≤ R) (hC0 : 0 ≤ C) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (hκ : ∀ j, 0 < κ j) (hk : ∀ j, k ≤ κ j)
    (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 2) 3)
    (hay : a ≤ ‖(physicalToNullCurrentPoint d x).2 none‖)
    (hR : ∀ j, κ j / ‖(physicalToNullCurrentPoint d x).2 none‖ ≤ R)
    (hC : ∀ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ≤ C)
    (hv : ∀ j, (∑ i, |v j i| ^ 2) ≤ 1 / 1600)
    (hr : OAI.Analysis.PDE.Green.physicalFullDefining d a x = 0)
    (hpoly : (Fintype.card ι : ℝ) * ((d : ℝ) + 1) *
      (R ^ ((d : ℝ) / 2) * C) ≤ h ^ (-b))
    (hlog : (b + M / 2) * Real.log h⁻¹ ≤ k * ‖(physicalToNullCurrentPoint d x).2 none‖ / 3200) :
    ‖star (OAI.Analysis.PDE.Dirichlet.quaternionGradient OAI.Analysis.Calculus.Quaternion.threeSlots (OAI.Analysis.PDE.Green.physicalFullDefining d a) x) ᵥ*
      physicalLatticeCurrent L h a κ cR cI v x‖ ≤
        (40 * ((d : ℝ) + 2) * ((d : ℝ) + 1) ^ 2) * h ^ (M - 1) := by
  let z := (physicalToNullCurrentPoint d x).2
  let q := (physicalToNullCurrentPoint d x).1
  have ha := hh.trans_le hha
  have hY : z none ≠ 0 := norm_pos_iff.mp (ha.trans_le hay)
  have hr' : OAI.Analysis.Calculus.Current.fiberDefining (1 / 10) a z = 0 :=
    (congrFun (physicalFullDefining_eq_null d a) x).symm.trans hr
  have hw := latticeWavePart_lateral_power_bound L h a R C k b M hh hR0 hC0
    κ cR cI v hκ hk q z hY hR hC hv hr' hpoly hlog
  have hg : ‖OAI.Analysis.Calculus.Current.fiberGradient (1 / 10) a z‖ ≤ 20 * ((d : ℝ) + 1) ^ 2 / h :=
    (OAI.Analysis.Calculus.Current.fiberGradient_norm_le a ha z hay hr'.le).trans
      (div_le_div_of_nonneg_left (by positivity) hh hha)
  have hn := latticeRegularizedCurrent_normal_flux_bound L h a κ cR cI v q z hY
  have hp := mul_le_mul (mul_le_mul_of_nonneg_left hg
    (show 0 ≤ (d : ℝ) + 2 by positivity)) hw (norm_nonneg _) (by positivity)
  have hb := hn.trans hp
  rw [physicalFullDefining_gradient d a x hY, physicalLatticeCurrent_eq_physicalMatrix]
  have hm := physicalMatrix_normal_row_bound
    (latticeRegularizedCurrent_isHermitian L h a hh κ cR cI v q z hY) (OAI.Analysis.Calculus.Current.fiberGradient (1 / 10) a z)
  refine hm.trans ((mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)).trans_eq ?_)
  rw [Real.rpow_sub hh, Real.rpow_one]
  ring

end OAI.Analysis.PDE.Concentration
