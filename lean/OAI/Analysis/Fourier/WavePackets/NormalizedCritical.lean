import OAI.Analysis.Fourier.WavePackets.Preprojection
import OAI.Analysis.Fourier.WavePackets.LogarithmicFactors
import OAI.Analysis.Fourier.WavePackets.RestrictedSector
import OAI.Analysis.Fourier.WavePackets.SectorFromPDE

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration
open scoped ENNReal ContDiff

local instance normalizedCriticalCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance normalizedCriticalCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance normalizedCriticalCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The sharp logarithmic periodic estimate for normalized inputs and
small semiclassical scales, conditional only on the concrete packet PDE
existence assertion above. The angular, amplitude, and energy estimates
are all constructed inside this proof. -/
theorem normalized_periodic_critical_of_packet_solvability {n : ℕ}
    (hsolve : PositivePacketSolvability n) {φ : Space (n + 2) → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    ∃ C h₀ : ℝ, 0 < C ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧
      ∀ h : ℝ, 0 < h → h ≤ h₀ →
        ∀ f : UnitAddTorus (Fin (n + 2)) → ℂ, Measurable f → Integrable f →
          let p : ℝ := 2 * (((n : ℝ) + 2) / ((n : ℝ) + 1))
          eLpNorm f (.ofReal p) volume ≤ 1 →
          eLpNorm (fun q : ℝ × UnitAddTorus (Fin (n + 2)) => periodicHalfWave φ h q.1 f q.2)
            (.ofReal p) (periodicSpacetimeMeasure (n + 2)) ≤
              ENNReal.ofReal (C * (1 + Real.log h⁻¹) ^ (2 * (n + 2) + 5)) := by
  let p : ℝ := 2 * (((n : ℝ) + 2) / ((n : ℝ) + 1))
  have hp : 2 ≤ p := by
    have hn : 0 < (n : ℝ) + 1 := by positivity
    have hh : 1 ≤ ((n : ℝ) + 2) / ((n : ℝ) + 1) := (le_div_iff₀ hn).mpr (by linarith)
    dsimp [p]
    linarith
  have hpe : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  obtain ⟨Cc, Ck, γ₀, K, hCc, hCk, hγ₀, hK, hKpos, hKvel, hpartition⟩ :=
    uniform_angular_partition hφ hc hz
  let A : ℝ := 4 * (n + 1 : ℕ) * γ₀
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨Cs, D, hs, hCs, hD, hhs, hhs1, hsector⟩ :=
    periodic_sector_bound_of_packet_solvability hsolve hK hKpos hKvel hA
  obtain ⟨ψ, B, Da, hψ, hcψ, hzψ, heψ, hB, hDa, hpre⟩ := uniform_preprojection hc hz
  let Craw : ℝ := Cc * (γ₀⁻¹) ^ (n + 1) * D ^ (((n + 1 : ℕ) : ℝ) / 2) * Da *
    (Cs * Ck ^ p * (2 : ℝ) ^ (p - 2)) ^ (1 / p) * B
  have hCraw : 0 ≤ Craw := by dsimp [Craw]; positivity
  refine ⟨Craw + 1, hs, by linarith, hhs, hhs1, ?_⟩
  intro h hh hsmall f hf hfi
  dsimp only
  intro hfn
  change eLpNorm f (.ofReal p) volume ≤ 1 at hfn
  change eLpNorm (fun q : ℝ × UnitAddTorus (Fin (n + 2)) => periodicHalfWave φ h q.1 f q.2)
    (.ofReal p) (periodicSpacetimeMeasure (n + 2)) ≤ _
  have hh1 : h ≤ 1 := hsmall.trans hhs1
  let L := OAI.Analysis.PDE.Concentration.packetLogScale D h
  let γ := logarithmicSectorWidth γ₀ L
  have hL1 : 1 ≤ L := one_le_packetLogScale hD hh hh1
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hγ := logarithmicSectorWidth_bounds hγ₀ hL1
  obtain ⟨I, hI, χ, R, hcard, hsum, hχ⟩ := hpartition γ hγ.1 hγ.2
  let : Fintype I := hI
  obtain ⟨N, hN, hNF⟩ := hpre h hh hh1
  obtain ⟨hFp, hFamp, hFpre⟩ := hNF (.ofReal p) hpe ENNReal.ofReal_ne_top f hf hfi hfn
  let F := periodicHalfWave ψ h 0 f
  have hF : Measurable F := by
    unfold F periodicHalfWave
    apply Measurable.tsum
    intro k
    exact (continuous_const.mul (UnitAddTorus.mFourier k).continuous).measurable
  have hχzero (i : I) : (0 : Space (n + 2)) ∉ tsupport (χ i) :=
    fun h0 => hz ((hχ i).2.2.1 h0)
  have hmix (i : I) (g : UnitAddTorus (Fin (n + 2)) → ℂ) :
      eLpNorm (fun q : ℝ × UnitAddTorus (Fin (n + 2)) => periodicHalfWave (χ i) h q.1 g q.2)
        (.ofReal p) (periodicSpacetimeMeasure (n + 2)) ^ p ≤
      ENNReal.ofReal (Cs * (1 + Real.log h⁻¹) ^ (p * (3 * ((n : ℝ) + 5) / 2))) *
        (eLpNorm (periodicHalfWave (χ i) h 0 g) ⊤ volume ^ (p - 2) *
          eLpNorm (periodicHalfWave (χ i) h 0 g) 2 volume ^ (2 : ℝ)) := by
    refine hsector h hh hsmall (R i) (χ i) (hχ i).2.1
      (fun ξ hξ => ((hχ i).2.2.2.2 ξ hξ).1) ?_ g
    intro ξ hξ
    have hv := ((hχ i).2.2.2.2 ξ hξ).2
    change Real.sqrt L * ‖OAI.Analysis.PDE.Concentration.gaussianVelocity ((OAI.Analysis.PDE.Concentration.spatialFinIsometry (n + 1)).symm (R i ξ))‖ ≤ A
    apply (mul_le_mul_of_nonneg_left hv (Real.sqrt_nonneg L)).trans
    have hcancel := logarithmicSectorWidth_cancel (γ₀ := γ₀) hL
    change Real.sqrt L * γ = γ₀ at hcancel
    calc
      Real.sqrt L * (4 * ↑(n + 1) * γ) = (4 * ↑(n + 1)) * (Real.sqrt L * γ) := by ring
      _ = A := by rw [hcancel]
      _ ≤ A := le_rfl
  have hout := periodic_bound_of_restricted_sectors Finset.univ χ
    (fun i _ => (hχ i).2.1) (fun i _ => (hχ i).1) (fun i _ => hχzero i)
    hh hF N hFamp hp (fun i _ => (hχ i).2.2.2.1)
    (fun i _ g _ _ => hmix i g)
  have hsum' : (∑ i ∈ Finset.univ, χ i) = φ := by
    funext ξ
    simpa only [Finset.sum_apply] using congrFun hsum ξ
  rw [hsum'] at hout
  have houtput : (fun q : ℝ × UnitAddTorus (Fin (n + 2)) => periodicHalfWave φ h q.1 F q.2) =
      (fun q : ℝ × UnitAddTorus (Fin (n + 2)) => periodicHalfWave φ h q.1 f q.2) := by
    funext q
    exact congrFun (hFpre q.1) q.2
  rw [houtput] at hout
  have hcardE : ((Finset.univ : Finset I).card : ℝ≥0∞) ≤ ENNReal.ofReal (Cc * (γ⁻¹) ^ (n + 1)) := by
    simpa only [Finset.card_univ, ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hcard
  have hNE : (N + 1 : ℝ≥0∞) ≤ ENNReal.ofReal (Da * (1 + Real.log h⁻¹)) := by
    simpa only [ENNReal.ofReal_add (Nat.cast_nonneg N) zero_le_one,
      ENNReal.ofReal_natCast, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hN
  have hFE : max 1 (eLpNorm F (.ofReal p) volume) ≤ ENNReal.ofReal B := by
    apply max_le _ hFp
    simpa using ENNReal.ofReal_le_ofReal hB
  apply hout.trans
  apply le_trans (mul_le_mul' (mul_le_mul' hcardE hNE) (mul_le_mul' le_rfl hFE))
  have hlog : 0 < 1 + Real.log h⁻¹ := by
    have := Real.log_nonneg ((one_le_inv₀ hh).mpr hh1)
    linarith
  have hfactors := assembled_log_factor (n + 1) hCc.le hDa.le hCs.le hCk
    (zero_le_one.trans hB) (zero_lt_one.trans_le hD) hγ₀ hp hlog
  have hexp : 2 * (n + 1) + 7 = 2 * (n + 2) + 5 := by omega
  have halpha : 3 * (((n + 1 : ℕ) : ℝ) + 4) / 2 = 3 * ((n : ℝ) + 5) / 2 := by push_cast; ring
  simp only [halpha, hexp] at hfactors
  change ENNReal.ofReal (Cc * (logarithmicSectorWidth γ₀ (D * (1 + Real.log h⁻¹)))⁻¹ ^ (n + 1)) *
    ENNReal.ofReal (Da * (1 + Real.log h⁻¹)) * _ ≤ _
  rw [hfactors]
  apply ENNReal.ofReal_le_ofReal
  change Craw * (1 + Real.log h⁻¹) ^ (2 * (n + 2) + 5) ≤ _
  exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hlog.le _)

end OAI.Analysis.Fourier.WavePackets
