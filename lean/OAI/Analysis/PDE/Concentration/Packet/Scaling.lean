import OAI.Analysis.PDE.Concentration.Packet.HalfWave

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current

theorem packetBaseWave_scale {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (s : ℝ)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    packetBaseWave κ (fun i => s * cR i) (fun i => s * cI i) v x y =
      (s : ℂ) * packetBaseWave κ cR cI v x y := by
  simp only [packetBaseWave, finiteWave, phaseComplex_eq_exp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  ring

theorem norm_packetBaseWave_scale {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) {s : ℝ} (hs : 0 ≤ s)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    ‖packetBaseWave κ (fun i => s * cR i) (fun i => s * cI i) v x y‖ =
      s * ‖packetBaseWave κ cR cI v x y‖ := by
  rw [packetBaseWave_scale, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]

def packetSupNorm {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) : ℝ :=
  sSup (Set.range (fun y => ‖packetBaseWave κ cR cI v 0 y‖))

theorem bddAbove_packet_norm {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) :
    BddAbove (Set.range (fun y => ‖packetBaseWave κ cR cI v 0 y‖)) := by
  refine ⟨∑ i, ‖OAI.Analysis.Calculus.Current.phaseComplex (cR i) (cI i) (OAI.Analysis.Calculus.Current.modeCovector (κ i) (v i)) 0‖, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact norm_finiteWave_le _ _ y

theorem norm_packet_le_sup {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    ‖packetBaseWave κ cR cI v 0 y‖ ≤ packetSupNorm κ cR cI v :=
  le_csSup (bddAbove_packet_norm κ cR cI v) (Set.mem_range_self y)

theorem packetSupNorm_nonneg {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) :
    0 ≤ packetSupNorm κ cR cI v :=
  (norm_nonneg _).trans (norm_packet_le_sup κ cR cI v 0)

theorem normalized_packet_norm_le {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (hP : 0 < packetSupNorm κ cR cI v) (y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    ‖packetBaseWave κ (fun i => (packetSupNorm κ cR cI v)⁻¹ * cR i)
      (fun i => (packetSupNorm κ cR cI v)⁻¹ * cI i) v 0 y‖ ≤ 1 := by
  rw [norm_packetBaseWave_scale κ cR cI v (inv_nonneg.mpr hP.le)]
  calc
    _ ≤ (packetSupNorm κ cR cI v)⁻¹ * packetSupNorm κ cR cI v :=
      mul_le_mul_of_nonneg_left (norm_packet_le_sup κ cR cI v y) (inv_nonneg.mpr hP.le)
    _ = 1 := inv_mul_cancel₀ hP.ne'

theorem normalized_packet_near_sup {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (hP : 0 < packetSupNorm κ cR cI v) {b : ℝ} (hb : b < 1) :
    ∃ y, b < ‖packetBaseWave κ (fun i => (packetSupNorm κ cR cI v)⁻¹ * cR i)
      (fun i => (packetSupNorm κ cR cI v)⁻¹ * cI i) v 0 y‖ ^ 2 := by
  by_cases hb0 : b < 0
  · exact ⟨0, hb0.trans_le (sq_nonneg _)⟩
  have hb0' : 0 ≤ b := le_of_not_gt hb0
  have hs : Real.sqrt b < 1 := by
    simpa using Real.sqrt_lt_sqrt hb0' hb
  have hlt : Real.sqrt b * packetSupNorm κ cR cI v < packetSupNorm κ cR cI v := by
    nlinarith
  obtain ⟨z, ⟨y, rfl⟩, hy⟩ := exists_lt_of_lt_csSup (Set.range_nonempty
    (fun y => ‖packetBaseWave κ cR cI v 0 y‖)) hlt
  refine ⟨y, ?_⟩
  rw [norm_packetBaseWave_scale κ cR cI v (inv_nonneg.mpr hP.le)]
  have hdiv : Real.sqrt b < (packetSupNorm κ cR cI v)⁻¹ * ‖packetBaseWave κ cR cI v 0 y‖ := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact (lt_div_iff₀ hP).mpr hy
  nlinarith [Real.sq_sqrt hb0', Real.sqrt_nonneg b]

theorem integral_rpow_packetBaseWave_scale {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) {s : ℝ} (hs : 0 ≤ s)
    (q : ℝ) (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (μ : Measure (OAI.Analysis.Calculus.Current.SpatialSpace d)) :
    (∫ y, ‖packetBaseWave κ (fun i => s * cR i) (fun i => s * cI i) v x y‖ ^ q ∂μ) =
      s ^ q * ∫ y, ‖packetBaseWave κ cR cI v x y‖ ^ q ∂μ := by
  simp_rw [norm_packetBaseWave_scale κ cR cI v hs,
    Real.mul_rpow hs (norm_nonneg _)]
  exact integral_const_mul _ _

theorem integral_sq_packetBaseWave_scale {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) {s : ℝ} (hs : 0 ≤ s)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (μ : Measure (OAI.Analysis.Calculus.Current.SpatialSpace d)) :
    (∫ y, ‖packetBaseWave κ (fun i => s * cR i) (fun i => s * cI i) v x y‖ ^ 2 ∂μ) =
      s ^ 2 * ∫ y, ‖packetBaseWave κ cR cI v x y‖ ^ 2 ∂μ := by
  simp_rw [norm_packetBaseWave_scale κ cR cI v hs, mul_pow]
  exact integral_const_mul _ _

end OAI.Analysis.PDE.Concentration
