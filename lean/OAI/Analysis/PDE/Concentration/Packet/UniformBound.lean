import OAI.Analysis.PDE.Concentration.UniformBarrier
import OAI.Analysis.PDE.Concentration.Packet.Solution
import OAI.Analysis.PDE.Concentration.Output.Normalized

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Filter Module Matrix OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped Topology ContDiff MatrixOrder ComplexOrder Matrix.Norms.Elementwise

/-- A deliberately coarse polynomial barrier, uniform on the entire
propagation domain and in the lattice and genuine Dirichlet solution. -/
theorem packet_solution_uniform_barrier (n : ℕ) (N K C : ℝ)
    (hN : 0 ≤ N) (hK : 0 ≤ K) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
      {ι : Type} [Fintype ι] (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
      (lam : ℝ), 0 < h → h ≤ 1 → h ≤ a → 0 ≤ lam →
      (∀ j, 0 < κ j) → (Fintype.card ι : ℝ) ≤ N / h ^ (n + 2) →
      (∀ j, κ j ≤ K / h) → (∀ j, ‖(⟨cR j, cI j⟩ : ℂ)‖ ≤ C) →
      (∀ j, (∑ i, |v j i| ^ 2) ≤ 1 / 1600) →
      ∀ S : PhysicalPacketSolution R h a κ cR cI v lam,
      ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain (n + 1) a,
        (B / h ^ (5 * (n + 2))) * OAI.Analysis.PDE.Green.physicalFullDefining (n + 1) a x ≤ S.u x := by
  obtain ⟨D, hD, hd⟩ := physical_packet_density_crude_bound (n + 1) N K C hN hK hC
  obtain ⟨c, hc, hb⟩ := physical_uniform_solution_bound n
  let B := (D + 1) / c
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro R ι inst h a κ cR cI v lam hh hh1 hha hlam hκ hcount hfreq hcoeff hv S x hx
  have ha : 0 < a := hh.trans_le hha
  obtain ⟨z, y, hxy⟩ : ∃ z y, x = OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z y := by
    refine ⟨(OAI.Analysis.PDE.Green.timeSpaceEquiv (n + 2) 3 x).1, (OAI.Analysis.PDE.Green.timeSpaceEquiv (n + 2) 3 x).2, ?_⟩
    rw [← OAI.Analysis.PDE.Green.timeSpaceEquiv_symm_apply, MeasurableEquiv.symm_apply_apply]
  subst x
  have hz : z ∈ physicalEnergyAnnulus a := by
    change a < ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ∧ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ < 4
    simpa only [OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber] using hx.1
  have hy : spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0 := by
    simpa only [OAI.Analysis.PDE.Green.physicalFullDefining, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber, spatialDefiningFunction,
      Function.comp_apply] using hx.2
  have hdensity (w : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 3)
      (hw : spatialDefiningFunction (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) w < 0) :
      (physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z w) 0 0).re ≤
        ((B / h ^ (5 * (n + 2))) * c) ^ (n + 1) := by
    have hdw := hd R h a κ cR cI v z w hh hh1 hha hz.1.le hκ hcount hfreq hcoeff hv hw.le
    have hp : 0 < h ^ (5 * (n + 2)) := pow_pos hh _
    have hp1 : h ^ (5 * (n + 2)) ≤ 1 := pow_le_one₀ hh.le hh1
    have he : B / h ^ (5 * (n + 2)) * c = (D + 1) / h ^ (5 * (n + 2)) := by
      dsimp only [B]
      field_simp
    rw [he]
    have hbase : 1 ≤ (D + 1) / h ^ (5 * (n + 2)) := (le_div_iff₀ hp).mpr (by linarith)
    have hpow : (D + 1) / h ^ (5 * (n + 2)) ≤
        ((D + 1) / h ^ (5 * (n + 2))) ^ (n + 1) := by
      rw [pow_succ]
      exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ hbase)
    exact hdw.trans ((div_le_div_of_nonneg_right (by linarith : D ≤ D + 1) hp.le).trans hpow)
  have hhbound := (hb a (OAI.Analysis.PDE.Green.energyComplexTime z) ha hz.1.le hz.2.le (packetSpatialBasis R)
    (fun w => S.u (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z w))
    (fun w => (physicalLatticeCurrent R h a κ cR cI v (OAI.Analysis.PDE.Green.fiberEmbedding (n + 2) 3 z w) 0 0).re)
    (B / h ^ (5 * (n + 2))) lam (by dsimp [B]; positivity) hlam
    ((S.fiber_smooth_interior z hz).of_le (by simp)) (S.fiber_smooth z hz).continuousOn
    (S.fiber_periodic z) (fun w hw => S.fiber_boundary hz hw)
    (fun w hw => S.fiber_equation ha hz hw) hdensity y hy.le).1
  simpa only [OAI.Analysis.PDE.Green.physicalFullDefining, OAI.Analysis.PDE.Green.fullPhysicalProjection_fiber, spatialDefiningFunction,
    Function.comp_apply] using hhbound

theorem normalized_packet_uniform_barrier {n : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))}
    (hK : IsCompact K) (hcap : ∀ η ∈ K, ‖gaussianVelocity η‖ ≤ 1 / 40) :
    ∃ B : ℝ, 0 < B ∧ ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)),
      (∀ j, ‖R (EuclideanSpace.single j 1)‖ ≤ 1) →
      ∀ {ι : Type} [Fintype ι] (h a : ℝ) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
      (m : ι → Option (Fin (n + 1)) → ℤ) (lam : ℝ),
      0 < h → h ≤ 1 → h ≤ a → 0 ≤ lam → Function.Injective m → (∀ j, 0 < κ j) →
      (∀ j i, inner ℝ (packetSpatialFrequency (κ j) (v j)) (R (EuclideanSpace.single i 1)) =
        (m j i : ℝ) * (2 * Real.pi) / 100) →
      (∀ j, h • packetSpatialFrequency (κ j) (v j) ∈ K) →
      (∀ y, ‖packetBaseWave κ cR cI v 0 y‖ ≤ 1) →
      ∀ S : PhysicalPacketSolution R h a κ cR cI v lam,
      ∀ x ∈ OAI.Analysis.PDE.Green.physicalPropagationDomain (n + 1) a,
        (B / h ^ (5 * (n + 2))) * OAI.Analysis.PDE.Green.physicalFullDefining (n + 1) a x ≤ S.u x := by
  obtain ⟨N, hN, hcount⟩ := compact_angular_frequency_count hK
  obtain ⟨F, hF, hfreq⟩ := compact_packet_frequency_bound hK
  obtain ⟨B, hB, hb⟩ := packet_solution_uniform_barrier n N F 1 hN.le hF.le (by norm_num)
  refine ⟨B, hB, ?_⟩
  intro R hR ι inst h a κ cR cI v m lam hh hh1 hha hlam hinj hκ hm hf hnorm
  apply hb R h a κ cR cI v lam hh hh1 hha hlam hκ
  · apply (le_div_iff₀ (pow_pos hh (n + 2))).mpr
    exact hcount R hR h hh hh1 _ m hinj hf hm
  · intro j; exact hfreq (v j) hh (hκ j) (hf j)
  · exact packet_coefficient_le_one R κ cR cI v m hinj hm hnorm
  · intro j; exact packet_velocity_bound (v j) hh (hκ j) (hcap _ (hf j))

end OAI.Analysis.PDE.Concentration
