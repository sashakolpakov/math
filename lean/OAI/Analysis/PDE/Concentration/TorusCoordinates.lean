import OAI.Analysis.PDE.Concentration.PeriodicPacket

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current OAI.Analysis.Fourier.WavePackets

local instance torusCoordinatesCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusCoordinatesCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance torusCoordinatesCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem integral_torus_reindex {D E : Type*} [Fintype D] [Fintype E]
    (e : D ≃ E) (f : UnitAddTorus E → ℝ) :
    (∫ x : UnitAddTorus D, f (fun i => x (e.symm i))) = ∫ y, f y := by
  have hm := volume_measurePreserving_piCongrLeft (fun _ : E => UnitAddCircle) e
  have he (x : UnitAddTorus D) :
      MeasurableEquiv.piCongrLeft (fun _ : E => UnitAddCircle) e x =
        fun i => x (e.symm i) := by
    funext i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  simpa only [he] using hm.integral_comp' f

theorem torusIndexedWave_reindex {D E ι : Type*} [Fintype D] [Fintype E] [Fintype ι]
    (e : D ≃ E) (m : ι → E → ℤ) (a : ι → ℂ) (x : UnitAddTorus D) :
    torusIndexedWave (fun j i => m j (e i)) a x =
      torusIndexedWave m a (fun i => x (e.symm i)) := by
  simp only [torusIndexedWave, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul, mFourier_reindex]

theorem integral_torusIndexedWave_reindex {D E ι : Type*} [Fintype D] [Fintype E] [Fintype ι]
    (e : D ≃ E) (m : ι → E → ℤ) (a : ι → ℂ) (F : ℂ → ℝ) :
    (∫ x, F (torusIndexedWave (fun j i => m j (e i)) a x)) =
      ∫ y, F (torusIndexedWave m a y) := by
  simp_rw [torusIndexedWave_reindex]
  exact integral_torus_reindex e (fun y => F (torusIndexedWave m a y))

theorem norm_torusIndexedWave_reindex {D E ι : Type*} [Fintype D] [Fintype E] [Fintype ι]
    (e : D ≃ E) (m : ι → E → ℤ) (a : ι → ℂ) :
    ‖torusIndexedWave (fun j i => m j (e i)) a‖ = ‖torusIndexedWave m a‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro x
    rw [torusIndexedWave_reindex]
    exact ContinuousMap.norm_coe_le_norm _ _
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro y
    have hb := ContinuousMap.norm_coe_le_norm
      (torusIndexedWave (fun j i => m j (e i)) a) (fun i => y (e i))
    simpa only [torusIndexedWave_reindex, Equiv.apply_symm_apply] using hb

theorem torusPacket_zero {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (m : ι → Option (Fin d) → ℤ) :
    torusPacket κ cR cI v m 0 = torusIndexedWave m (fun j => cR j + cI j * Complex.I) := by
  simp [torusPacket, phaseComplex_eq_exp, OAI.Analysis.Calculus.Current.phaseArgument]

theorem packetSupNorm_eq_fin_torus_norm {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (m : ι → Option (Fin d) → ℤ)
    (hm : ∀ j i, inner ℝ (packetSpatialFrequency (κ j) (v j)) (R (EuclideanSpace.single i 1)) =
      (m j i : ℝ) * (2 * Real.pi) / 100) :
    packetSupNorm κ cR cI v =
      ‖torusIndexedWave (fun j i => m j (finSuccEquiv d i)) (fun j => cR j + cI j * Complex.I)‖ := by
  rw [packetSupNorm_eq_torus_norm R κ cR cI v m hm, torusPacket_zero,
    norm_torusIndexedWave_reindex]

theorem integral_packetBaseWave_zero_eq_fin_torus {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (m : ι → Option (Fin d) → ℤ)
    (hm : ∀ j i, inner ℝ (packetSpatialFrequency (κ j) (v j)) (R (EuclideanSpace.single i 1)) =
      (m j i : ℝ) * (2 * Real.pi) / 100) (F : ℂ → ℝ) :
    (∫ y in physicalSpatialCell R, F (packetBaseWave κ cR cI v 0 y)) =
      |LinearMap.det (spatialCellMap R).toLinearMap| *
        ∫ x, F (torusIndexedWave (fun j i => m j (finSuccEquiv d i))
          (fun j => cR j + cI j * Complex.I) x) := by
  rw [integral_packetBaseWave_eq_torus R κ cR cI v m hm, torusPacket_zero,
    integral_torusIndexedWave_reindex]

theorem integral_packetBaseWave_eq_periodicHalfWave {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃ₗᵢ[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (m : ι → Option (Fin d) → ℤ)
    (hinj : Function.Injective m) (hκ : ∀ i, 0 ≤ κ i)
    (hm : ∀ j i, inner ℝ (packetSpatialFrequency (κ j) (v j)) (R (EuclideanSpace.single i 1)) =
      (m j i : ℝ) * (2 * Real.pi) / 100)
    (φ : EuclideanSpace ℝ (Fin (d + 1)) → ℂ) (h t : ℝ)
    (hφ : ∀ j, φ (h • OAI.Analysis.Fourier.WavePackets.periodicFrequency (fun i => m j (finSuccEquiv d i))) = 1) (F : ℂ → ℝ) :
    (∫ y in physicalSpatialCell R.toContinuousLinearEquiv,
      F (packetBaseWave κ cR cI v (physicalNullTime d t) y)) =
      |LinearMap.det (spatialCellMap R.toContinuousLinearEquiv).toLinearMap| *
        ∫ x, F (OAI.Analysis.Fourier.WavePackets.periodicHalfWave φ h t
          (torusIndexedWave (fun j i => m j (finSuccEquiv d i)) (fun j => cR j + cI j * Complex.I)) x) := by
  rw [integral_packetBaseWave_eq_torus R.toContinuousLinearEquiv κ cR cI v m hm,
    ← integral_torus_reindex (finSuccEquiv d)]
  simp_rw [periodicHalfWave_eq_packet R κ cR cI v m hinj hκ hm φ h t hφ]

end OAI.Analysis.PDE.Concentration
