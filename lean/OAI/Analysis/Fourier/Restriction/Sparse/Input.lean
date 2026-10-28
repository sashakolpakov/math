import OAI.Analysis.Fourier.Restriction.Sparse.Identity

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem localSmoothing_sparse_input_norm (hls : OAI.Analysis.Fourier.LocalSmoothing.EuclideanLocalSmoothing)
    {n : ℕ} (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (u : SchwartzMap (Space n) ℂ) (c : ℝ), 0 < c →
      (∀ x, ‖x‖ ≤ 1 → c ≤ ‖u x‖) → ∀ (N : ℕ) (R : ℝ), 1 ≤ R →
      ∀ z : Fin N → Space n,
      Pairwise (fun i j ↦ Disjoint (ball (z i) R) (ball (z j) R)) →
      ∀ f : Space n → ℂ, Measurable f → Integrable f →
      eLpNorm (fun p : Fin N × Space n ↦ OAI.Analysis.Fourier.LocalSmoothing.angularFourier (sparsePiece u R (z p.1) f) p.2)
        (ENNReal.ofReal (restrictionInputExponent n))
        (Measure.count.prod (volume.restrict (sphericalAnnulus ((2 * R)⁻¹)))) ≤
      C * ENNReal.ofReal ((2 * R)⁻¹) ^ (1 / restrictionInputExponent n) *
        ENNReal.ofReal (R ^ ε) * ENNReal.ofReal c⁻¹ *
        eLpNorm f (ENNReal.ofReal (restrictionInputExponent n)) volume := by
  obtain ⟨C, hC, HC⟩ := localSmoothing_thin_annulus hls hn hε
  refine ⟨C, hC, ?_⟩
  intro u c hc hu N R hR z hd f hfm hfi
  let g (i : Fin N) := sparsePiece u R (z i) f
  let ν := volume.restrict (sphericalAnnulus (n := n) ((2 * R)⁻¹))
  have : IsFiniteMeasure ν := sparse_annulus_finite hR
  have hR0 : 0 < R := by linarith
  have hp : 0 < restrictionInputExponent n := lt_trans zero_lt_one (restrictionInputExponent_bounds hn).1
  have hgi (i : Fin N) : Integrable (g i) := integrable_sparsePiece u hc hR0 hu (z i) hfm hfi
  have hgm (i : Fin N) : Measurable (g i) := measurable_sparsePiece u R (z i) hfm
  have H := eLpNorm_finite_family_bound ν (measurable_finite_fourier g hgi) hp
    (fun i ↦ eLpNorm (g i) (ENNReal.ofReal (restrictionInputExponent n)) volume)
    (C * ENNReal.ofReal ((2 * R)⁻¹) ^ (1 / restrictionInputExponent n) * ENNReal.ofReal (R ^ ε))
    (fun i ↦ HC R hR (g i) (hgm i) (hgi i) (sparsePiece_support u R (z i) f)
      ((2 * R)⁻¹) (sparse_annulus_width hR).1 (sparse_annulus_width hR).2)
  apply H.trans
  calc
    _ ≤ (C * ENNReal.ofReal ((2 * R)⁻¹) ^ (1 / restrictionInputExponent n) * ENNReal.ofReal (R ^ ε)) *
        (ENNReal.ofReal c⁻¹ * eLpNorm f (ENNReal.ofReal (restrictionInputExponent n)) volume) :=
      mul_le_mul' le_rfl (sparsePiece_Lp_sum_le u hc hR0 hu z hd hfm hp)
    _ = _ := by ring

end OAI.Analysis.Fourier.Restriction
