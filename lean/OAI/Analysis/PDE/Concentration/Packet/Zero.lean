import OAI.Analysis.PDE.Concentration.Packet.Normalization
import OAI.Analysis.PDE.Concentration.Packet.Scaling

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current

/-- Distinct quantized frequencies make a packet with zero initial
supremum identically zero at every time, by exact Parseval. -/
theorem packet_zero_of_supNorm_zero {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (m : ι → Option (Fin d) → ℤ)
    (hinj : Function.Injective m)
    (hm : ∀ j i, inner ℝ (packetSpatialFrequency (κ j) (v j)) (R (EuclideanSpace.single i 1)) =
      (m j i : ℝ) * (2 * Real.pi) / 100)
    (hP : packetSupNorm κ cR cI v = 0) (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    packetBaseWave κ cR cI v x y = 0 := by
  have hz (y : OAI.Analysis.Calculus.Current.SpatialSpace d) : packetBaseWave κ cR cI v 0 y = 0 := by
    apply norm_eq_zero.mp
    exact le_antisymm ((norm_packet_le_sup κ cR cI v y).trans_eq hP) (norm_nonneg _)
  have hE : (∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v 0 y‖ ^ 2) = 0 := by
    simp [hz]
  rw [integral_sq_packetBaseWave R κ cR cI v m hinj hm 0] at hE
  have hJ : 0 < |LinearMap.det (spatialCellMap R).toLinearMap| := by
    rw [← physicalSpatialCell_volume]
    exact physicalSpatialCell_volume_pos R
  have hsum : (∑ i, ‖(⟨cR i, cI i⟩ : ℂ)‖ ^ 2) = 0 :=
    (mul_eq_zero.mp hE).resolve_left hJ.ne'
  have hc (i : ι) : ‖(⟨cR i, cI i⟩ : ℂ)‖ = 0 := by
    have hi := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) => sq_nonneg ‖(⟨cR j, cI j⟩ : ℂ)‖) (Finset.mem_univ i)
    rw [hsum] at hi
    nlinarith [norm_nonneg (⟨cR i, cI i⟩ : ℂ)]
  unfold packetBaseWave finiteWave
  apply Finset.sum_eq_zero
  intro i hi
  have hp : OAI.Analysis.Calculus.Current.phaseComplex (cR i) (cI i) (OAI.Analysis.Calculus.Current.modeCovector (κ i) (v i)) x = 0 := by
    apply norm_eq_zero.mp
    rw [OAI.Analysis.Calculus.Current.phaseComplex_norm, hc]
  dsimp only
  rw [hp, zero_mul]

end OAI.Analysis.PDE.Concentration
