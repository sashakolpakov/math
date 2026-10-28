import OAI.Analysis.PDE.Concentration.Input.Integrability
import OAI.Analysis.PDE.Concentration.Input.Sector

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open _root_.MeasureTheory Set OAI.Analysis.Calculus.Current

/-- Sharp integrated input-density bound with an arbitrary bounded
nonnegative weight. In the energy argument the weight is the actual `-u`;
its bound is supplied by the proved Dirichlet comparison theorem. -/
theorem packet_weighted_input_density {d : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d)
      (h L : ℝ), 0 < h → 1 ≤ L → ∀ {ι : Type} [Fintype ι]
      (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (m : ι → Option (Fin d) → ℤ),
      Function.Injective m → (∀ k, 0 < κ k) →
      (∀ k i, inner ℝ (packetSpatialFrequency (κ k) (v k)) (R (EuclideanSpace.single i 1)) =
        (m k i : ℝ) * (2 * Real.pi) / 100) →
      (∀ k, h • packetSpatialFrequency (κ k) (v k) ∈ K) →
      (∀ k, Real.sqrt L * ‖gaussianVelocity (h • packetSpatialFrequency (κ k) (v k))‖ ≤ A) →
      ∀ (x : OAI.Analysis.Calculus.Current.Index d → ℝ) (τ : ℂ), h * L ≤ ‖τ‖ → ‖τ‖ ≤ 4 * (h * L) →
      ∀ (w : (Option (Fin d) → ℂ) → OAI.Analysis.Calculus.Current.SpatialSpace d → ℝ) (B : ℝ), 0 ≤ B →
      (∀ q, OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) (h * L) τ q < 0 →
        ∀ y, 0 ≤ w q y ∧ w q y ≤ B) →
      (∫ q in {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) (h * L) τ q < 0},
        ∫ y in physicalSpatialCell R, w q y *
          OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h (h * L) κ cR cI v
            (x - nullSpatialShift y) (OAI.Analysis.Calculus.Current.physicalEmbedding τ q))) ≤
        C * B * (h ^ 2 * L ^ (d + 2) * (∫ y in physicalSpatialCell R, ‖packetBaseWave κ cR cI v x y‖ ^ 2) +
          volume.real (physicalSpatialCell R) * h ^ (50 * (d + 1))) := by
  obtain ⟨C, hC, hbound⟩ := packet_sector_input_density hK hpos A hA
  refine ⟨C, hC, ?_⟩
  intro R h L hh hL ι _ κ cR cI v m hinj hκ hm hfreq hsector x τ ht ht' w B hB hw
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have ha : 0 < h * L := mul_pos hh hL0
  let S := {q : Option (Fin d) → ℂ | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) (h * L) τ q < 0}
  have hS : MeasurableSet S := (OAI.Analysis.PDE.Green.isOpen_physical_fiber (h * L) τ ha ht).measurableSet
  have hi := integrable_packet_input_density R h (h * L) hh κ cR cI v x τ ha ht
  have hweighted := weighted_double_integral_le hi
    (by
      filter_upwards [ae_restrict_mem hS] with q hq
      filter_upwards [] with y
      have hr : OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) (h * L) τ q ≤ 0 := hq.le
      have hy := (physical_input_height (h * L) τ q ha ht ht' hr).1
      exact (latticeRegularizedCurrent_time_pos R h (h * L) hh ha.ne' κ cR cI v _ _
        (norm_ne_zero_iff.mp (ha.trans_le hy).ne') hr).le)
    (by
      filter_upwards [ae_restrict_mem hS] with q hq
      exact Filter.Eventually.of_forall fun y => hw q hq y)
  have hraw := hbound R h L hh hL κ cR cI v m hinj hκ hm hfreq hsector x τ ht ht'
  apply hweighted.trans
  convert mul_le_mul_of_nonneg_left hraw hB using 1 ; ring

end OAI.Analysis.PDE.Concentration
