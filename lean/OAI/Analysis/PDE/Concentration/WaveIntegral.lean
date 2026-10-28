import OAI.Analysis.PDE.Concentration.Packet.HalfWave
import OAI.Analysis.PDE.Concentration.CellBoundary
import OAI.Analysis.PDE.Concentration.Cylinder.Monotone

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.Calculus.Current
open scoped ContDiff

theorem norm_packetBaseWave_le {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    ‖packetBaseWave κ cR cI v x y‖ ≤ ∑ i, ‖(⟨cR i, cI i⟩ : ℂ)‖ := by
  have h := norm_finiteWave_le (fun i => packetCycleFrequency (κ i) (v i))
    (fun i => OAI.Analysis.Calculus.Current.phaseComplex (cR i) (cI i) (OAI.Analysis.Calculus.Current.modeCovector (κ i) (v i)) x) y
  simpa only [packetBaseWave, OAI.Analysis.Calculus.Current.phaseComplex_norm] using h

theorem continuous_packet_power {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (hκ : ∀ i, 0 ≤ κ i) {p : ℝ} (hp : 0 ≤ p) :
    Continuous (fun z : ℝ × OAI.Analysis.Calculus.Current.SpatialSpace d =>
      ‖packetBaseWave κ cR cI v (physicalNullTime d z.1) z.2‖ ^ p) :=
  (contDiff_packetBaseWave_time_space κ cR cI v hκ).continuous.norm.rpow_const
    (fun _ => Or.inr hp)

theorem packet_power_bound {d : ℕ} {ι : Type*} [Fintype ι]
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) {p : ℝ} (hp : 0 ≤ p)
    (t : ℝ) (y : OAI.Analysis.Calculus.Current.SpatialSpace d) :
    ‖‖packetBaseWave κ cR cI v (physicalNullTime d t) y‖ ^ p‖ ≤
      (∑ i, ‖(⟨cR i, cI i⟩ : ℂ)‖) ^ p := by
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  exact Real.rpow_le_rpow (norm_nonneg _) (norm_packetBaseWave_le κ cR cI v _ _) hp

theorem continuous_setIntegral_of_uniform_bound {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {μ : Measure E}
    {S : Set E} (hS : μ S ≠ ⊤) {f : ℝ × E → ℝ} (hf : Continuous f)
    (B : ℝ) (hB : ∀ t y, ‖f (t, y)‖ ≤ B) :
    Continuous (fun t => ∫ y in S, f (t, y) ∂μ) := by
  apply continuous_of_dominated (bound := fun _ => B)
  · intro t
    exact (hf.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro t
    exact Filter.Eventually.of_forall (hB t)
  · exact integrableOn_const hS
  · exact Filter.Eventually.of_forall (fun y => hf.comp (continuous_id.prodMk continuous_const))

theorem continuous_packet_spatial_integral {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) {p : ℝ} (hp : 0 ≤ p) :
    Continuous (fun t => ∫ y in physicalSpatialCell R,
      ‖packetBaseWave κ cR cI v (physicalNullTime d t) y‖ ^ p) := by
  have hc := continuous_setIntegral_of_uniform_bound
    (μ := (volume : Measure (OAI.Analysis.Calculus.Current.SpatialSpace d)))
    (isCompact_closedPhysicalSpatialCell R).measure_lt_top.ne
    (continuous_packet_power κ cR cI v hκ hp)
    ((∑ i, ‖(⟨cR i, cI i⟩ : ℂ)‖) ^ p) (packet_power_bound κ cR cI v hp)
  simpa only [integral_closedPhysicalSpatialCell] using hc

/-- Integrate a pointwise output lower bound along the whole cylindrical
observation surface, retaining its exact angular length. -/
theorem cylinder_integral_lower_of_time_bound {F : CylinderSpace → ℝ} {U : Set CylinderSpace}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hKU : cylinderShell 1 2 ρ ρ ⊆ U) {W : ℝ → ℝ} (hW : Continuous W) (d : ℝ)
    (hbound : ∀ t ∈ Icc (1 : ℝ) 2, ∀ θ, d * W t ≤ F (cylinderPoint t ρ θ)) :
    (2 * Real.pi) * d * (∫ t in (1 : ℝ)..2, W t) ≤
      ∫ t in (1 : ℝ)..2, ∫ θ in (0 : ℝ)..(2 * Real.pi), F (cylinderPoint t ρ θ) := by
  obtain ⟨G, hG, heG⟩ := exists_global_smooth_eq_near_closed
    (isCompact_cylinderShell 1 2 ρ ρ).isClosed hU hKU hF
  have he (t : ℝ) (ht : t ∈ Icc (1 : ℝ) 2) (θ : ℝ) :
      G (cylinderPoint t ρ θ) = F (cylinderPoint t ρ θ) :=
    (heG _ (cylinderPoint_mem_shell ht ⟨le_rfl, le_rfl⟩ hρ)).eq_of_nhds
  have hGc : Continuous (fun t => cylinderAngularAverage G t ρ) :=
    (contDiff_cylinderAngularAverage hG).continuous.comp (continuous_id.prodMk continuous_const)
  have hWc : Continuous (fun t => (2 * Real.pi) * (d * W t)) :=
    continuous_const.mul (continuous_const.mul hW)
  have hh := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (1 : ℝ) ≤ 2)
    (hWc.intervalIntegrable 1 2)
    (hGc.intervalIntegrable 1 2) (fun t ht => by
      have hc : Continuous (fun θ => G (cylinderPoint t ρ θ)) :=
        (contDiff_cylinder_time_angle hG ρ).continuous.comp (continuous_const.prodMk continuous_id)
      have hi := intervalIntegral.integral_mono_on (μ := volume)
        (f := fun _ : ℝ => d * W t) (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
        (continuous_const.intervalIntegrable 0 (2 * Real.pi))
        (hc.intervalIntegrable 0 (2 * Real.pi)) (fun θ hθ => by rw [he t ht θ]; exact hbound t ht θ)
      simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, cylinderAngularAverage]
        using hi)
  have heint : (∫ t in (1 : ℝ)..2, cylinderAngularAverage G t ρ) =
      ∫ t in (1 : ℝ)..2, ∫ θ in (0 : ℝ)..(2 * Real.pi), F (cylinderPoint t ρ θ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply intervalIntegral.integral_congr
    intro θ hθ
    exact he t (by simpa using ht) θ
  rw [heint] at hh
  simpa only [intervalIntegral.integral_const_mul, mul_assoc] using hh

end OAI.Analysis.PDE.Concentration
