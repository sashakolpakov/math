import OAI.Analysis.PDE.Concentration.Packet.L2
import OAI.Analysis.PDE.Concentration.Packet.Scaling

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current

local instance torusPacketCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance torusPacketCircleHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance torusPacketCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

def torusPacket {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (m : ι → Option (Fin d) → ℤ)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) : C(UnitAddTorus (Option (Fin d)), ℂ) :=
  torusIndexedWave m (fun i => OAI.Analysis.Calculus.Current.phaseComplex (cR i) (cI i) (OAI.Analysis.Calculus.Current.modeCovector (κ i) (v i)) x)

theorem packetBaseWave_spatialCoordinates {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (m : ι → Option (Fin d) → ℤ)
    (hm : ∀ j i, inner ℝ (packetSpatialFrequency (κ j) (v j)) (R (EuclideanSpace.single i 1)) =
      (m j i : ℝ) * (2 * Real.pi) / 100)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (y : Option (Fin d) → ℝ) :
    packetBaseWave κ cR cI v x ((100 : ℝ) • R (spatialFromCoordinates y)) =
      torusPacket κ cR cI v m x (fun i => (y i : UnitAddCircle)) :=
  finiteWave_spatialCoordinates R _ m _
    (fun j => packetCycleFrequency_basis R (κ j) (v j) (m j) (hm j)) y

theorem integral_packetBaseWave_eq_torus {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (m : ι → Option (Fin d) → ℤ)
    (hm : ∀ j i, inner ℝ (packetSpatialFrequency (κ j) (v j)) (R (EuclideanSpace.single i 1)) =
      (m j i : ℝ) * (2 * Real.pi) / 100)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (F : ℂ → ℝ) :
    (∫ y in physicalSpatialCell R, F (packetBaseWave κ cR cI v x y)) =
      |LinearMap.det (spatialCellMap R).toLinearMap| *
        ∫ z, F (torusPacket κ cR cI v m x z) := by
  rw [integral_physicalSpatialCell,
    UnitAddTorus.integral_preimage (fun z => F (torusPacket κ cR cI v m x z)) (fun _ => 0)]
  simp only [zero_add]
  congr 1
  apply setIntegral_congr_fun (MeasurableSet.univ_pi' fun _ => measurableSet_Ioc)
  intro y hy
  dsimp only
  rw [packetBaseWave_spatialCoordinates R κ cR cI v m hm]

theorem packet_spatial_range_eq_torus_range {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (m : ι → Option (Fin d) → ℤ)
    (hm : ∀ j i, inner ℝ (packetSpatialFrequency (κ j) (v j)) (R (EuclideanSpace.single i 1)) =
      (m j i : ℝ) * (2 * Real.pi) / 100)
    (x : OAI.Analysis.Calculus.Current.Index d → ℝ) :
    Set.range (packetBaseWave κ cR cI v x) = Set.range (torusPacket κ cR cI v m x) := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    let u : Option (Fin d) → ℝ := ((100 : ℝ)⁻¹ • R.symm y).ofLp
    refine ⟨fun i => (u i : UnitAddCircle), ?_⟩
    rw [← packetBaseWave_spatialCoordinates R κ cR cI v m hm]
    have hu : spatialFromCoordinates u = (100 : ℝ)⁻¹ • R.symm y := rfl
    rw [hu, map_smul, R.apply_symm_apply, smul_smul]
    norm_num
  · rintro ⟨z, rfl⟩
    choose y hy using fun i => Quotient.exists_rep (z i)
    refine ⟨(100 : ℝ) • R (spatialFromCoordinates y), ?_⟩
    rw [packetBaseWave_spatialCoordinates R κ cR cI v m hm]
    congr 1
    funext i
    exact hy i

theorem packetSupNorm_eq_torus_norm {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (m : ι → Option (Fin d) → ℤ)
    (hm : ∀ j i, inner ℝ (packetSpatialFrequency (κ j) (v j)) (R (EuclideanSpace.single i 1)) =
      (m j i : ℝ) * (2 * Real.pi) / 100) :
    packetSupNorm κ cR cI v = ‖torusPacket κ cR cI v m 0‖ := by
  have hr := packet_spatial_range_eq_torus_range R κ cR cI v m hm 0
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro b ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hr.subset (Set.mem_range_self y)
    dsimp only
    rw [← hz]
    exact ContinuousMap.norm_coe_le_norm _ _
  · apply (ContinuousMap.norm_le _ (packetSupNorm_nonneg κ cR cI v)).mpr
    intro z
    obtain ⟨y, hy⟩ := hr.symm.subset (Set.mem_range_self z)
    rw [← hy]
    exact norm_packet_le_sup κ cR cI v y

end OAI.Analysis.PDE.Concentration
