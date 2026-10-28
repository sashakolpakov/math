import OAI.Analysis.PDE.Concentration.Output.Sector
import OAI.Analysis.PDE.Concentration.Output.Coordinates
import OAI.Analysis.PDE.Concentration.Output.BallGeometry

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Metric OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green

/-- The source's output recovery lower bound holds on every full physical
`h`-ball over the output patch. The ball inclusion and all coordinate and
cutoff conditions are proved internally. -/
theorem packet_output_full_ball {d : ℕ} {K : Set (OAI.Analysis.Calculus.Current.SpatialSpace d)}
    (hK : IsCompact K) (hpos : ∀ η ∈ K, 0 < gaussianFrequencyK η)
    (hv : ∀ η ∈ K, ‖gaussianVelocity η‖ < 1) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C L₀ : ℝ, 0 < C ∧ 10000 ≤ L₀ ∧
      ∀ (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h L : ℝ), 0 < h → L₀ ≤ L →
      ∀ {ι : Type} [Fintype ι] (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ),
      (∀ k, 0 < κ k) →
      (∀ k i, ∃ m : ℤ, inner ℝ (packetSpatialFrequency (κ k) (v k))
        (R (EuclideanSpace.single i 1)) = (m : ℝ) * (2 * Real.pi) / 100) →
      (∀ k, h • packetSpatialFrequency (κ k) (v k) ∈ K) →
      (∀ k, Real.sqrt L * ‖gaussianVelocity (h • packetSpatialFrequency (κ k) (v k))‖ ≤ A) →
      ∀ z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3, h * L ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ →
      ‖OAI.Analysis.PDE.Green.energyComplexTime z‖ ≤ 4 * (h * L) →
      ∀ (y : OAI.Analysis.Calculus.Current.SpatialSpace d) (q : Option (Fin d) → ℂ),
      q ∈ physicalOutputPatch (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) (Real.sqrt L)⁻¹ →
      closedBall (spatialPacketEmbedding d y q) h ⊆
        {x | spatialDefiningFunction d (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) x < 0} ∧
      ∀ x ∈ closedBall (spatialPacketEmbedding d y q) h,
      ‖packetBaseWave κ cR cI v (physicalNullTime d (z (0, 0))) y‖ ^ 2 ≤
        C * h ^ (2 * d) * L ^ ((gaussianDerivativeOrder d : ℝ) + d) *
          (physicalLatticeCurrent R h (h * L) κ cR cI v
            (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z x) 0 0).re := by
  obtain ⟨C, hC, hb⟩ := packet_sector_density_recovery hK hpos hv A hA
  obtain ⟨L₀, hL₀, hgeom⟩ := output_full_ball_geometry d
  refine ⟨C, L₀, hC, hL₀, ?_⟩
  intro R h L hh hL ι _ κ cR cI v hκ hm hf hs z ht ht' y q hq
  obtain ⟨p, hp, rfl⟩ := hq
  have hg (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3)
      (hx : x ∈ closedBall (spatialPacketEmbedding d y
        (OAI.Analysis.Calculus.Current.physicalFiberInverse (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) p)) h) :=
    hgeom h L (OAI.Analysis.PDE.Green.energyComplexTime z) hh hL ht ht' y p hp x
      (show ‖x - spatialPacketEmbedding d y (OAI.Analysis.Calculus.Current.physicalFiberInverse (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) p)‖ ≤ h from
        by simpa only [mem_closedBall, dist_eq_norm] using hx)
  refine ⟨fun x hx => (hg x hx).1, ?_⟩
  intro x hx
  have hdist : ‖y - physicalSpatialRealVector d x‖ ≤ h := by
    rw [norm_sub_rev]
    have hd := physicalSpatialRealVector_distance d x
      (spatialPacketEmbedding d y (OAI.Analysis.Calculus.Current.physicalFiberInverse (h * L) (OAI.Analysis.PDE.Green.energyComplexTime z) p))
    rw [spatialPacketEmbedding_real] at hd
    exact hd.trans (by simpa only [mem_closedBall, dist_eq_norm] using hx)
  rw [physicalLatticeCurrent_output_density]
  apply hb R h L hh (hL₀.trans hL) κ cR cI v hκ hm hf hs
    (physicalNullTime d (z (0, 0))) (OAI.Analysis.PDE.Green.energyComplexTime z) ht ht'
    (OAI.Analysis.PDE.Green.physicalSpatialProjection d x) (hg x hx).1.le (hg x hx).2.2.1 (hg x hx).2.2.2
    y (physicalSpatialRealVector d x) hdist

end OAI.Analysis.PDE.Concentration
