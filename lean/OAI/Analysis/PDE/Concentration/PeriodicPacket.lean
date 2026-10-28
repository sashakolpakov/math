import OAI.Analysis.PDE.Concentration.TorusPacket
import OAI.Analysis.Fourier.WavePackets.FiniteFourier

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Fourier.WavePackets

local instance periodicPacketCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance periodicPacketCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance periodicPacketCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem mFourier_reindex {D E : Type*} [Fintype D] [Fintype E]
    (e : D ≃ E) (m : E → ℤ) (x : UnitAddTorus D) :
    UnitAddTorus.mFourier (fun i => m (e i)) x =
      UnitAddTorus.mFourier m (fun i => x (e.symm i)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  simpa only [Equiv.symm_apply_apply] using
    e.prod_comp (fun i => fourier (m i) (x (e.symm i)))

theorem norm_frequency_of_isometric_quantization {d : ℕ}
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃ₗᵢ[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (ω : OAI.Analysis.Calculus.Current.SpatialSpace d)
    (m : Option (Fin d) → ℤ)
    (hm : ∀ i, inner ℝ ω (R (EuclideanSpace.single i 1)) =
      (m i : ℝ) * (2 * Real.pi) / 100) :
    ‖ω‖ = ‖OAI.Analysis.Fourier.WavePackets.periodicFrequency (fun i => m (finSuccEquiv d i))‖ := by
  have hc (i : Option (Fin d)) : R.symm ω i = (m i : ℝ) * (2 * Real.pi) / 100 := by
    have hi := R.inner_map_map (R.symm ω) (EuclideanSpace.single i 1)
    rw [R.apply_symm_apply, hm] at hi
    simpa only [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul] using hi.symm
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← R.symm.norm_map ω, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  rw [← (finSuccEquiv d).sum_comp (fun i => ‖R.symm ω i‖ ^ 2)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hc]
  congr 2
  change (m (finSuccEquiv d i) : ℝ) * (2 * Real.pi) / 100 =
    (2 * Real.pi / 100) * (m (finSuccEquiv d i) : ℝ)
  ring

/-- Exact identification of a rotated physical packet with the actual
side-100 periodic half-wave multiplier. The cutoff equals one on the packet;
the rotation is not restricted to an axis-aligned lattice. -/
theorem periodicHalfWave_eq_packet {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃ₗᵢ[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (m : ι → Option (Fin d) → ℤ)
    (hinj : Function.Injective m) (hκ : ∀ i, 0 ≤ κ i)
    (hm : ∀ j i, inner ℝ (packetSpatialFrequency (κ j) (v j)) (R (EuclideanSpace.single i 1)) =
      (m j i : ℝ) * (2 * Real.pi) / 100)
    (φ : EuclideanSpace ℝ (Fin (d + 1)) → ℂ) (h t : ℝ)
    (hφ : ∀ j, φ (h • OAI.Analysis.Fourier.WavePackets.periodicFrequency (fun i => m j (finSuccEquiv d i))) = 1)
    (x : UnitAddTorus (Fin (d + 1))) :
    OAI.Analysis.Fourier.WavePackets.periodicHalfWave φ h t
      (torusIndexedWave (fun j i => m j (finSuccEquiv d i)) (fun j => cR j + cI j * Complex.I)) x =
      torusPacket κ cR cI v m (physicalNullTime d t)
        (fun i => x ((finSuccEquiv d).symm i)) := by
  have hm' : Function.Injective (fun j i => m j (finSuccEquiv d i)) := by
    intro i j hij
    apply hinj
    funext k
    have hh := congrFun hij ((finSuccEquiv d).symm k)
    simpa only [Equiv.apply_symm_apply] using hh
  rw [OAI.Analysis.Fourier.WavePackets.periodicHalfWave_torusIndexedWave φ h t _ hm']
  simp only [torusPacket, torusIndexedWave, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [OAI.Analysis.Fourier.WavePackets.periodicSymbol, hφ, mul_one, mFourier_reindex,
    phaseComplex_eq_exp, phaseArgument_physicalNullTime (hκ j),
    norm_frequency_of_isometric_quantization R _ (m j) (hm j)]
  push_cast
  congr 1
  rw [mul_comm]
  congr 1
  congr 1
  ring

end OAI.Analysis.PDE.Concentration
