import OAI.Analysis.PDE.Concentration.Physical.Lipschitz
import OAI.Analysis.PDE.Concentration.Output.Threshold
import OAI.Analysis.PDE.Concentration.Packet.Coordinates

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green

/-- Every full real fiber `h`-ball centered over the small output patch lies
strictly inside the fiber and in the larger Gaussian-recovery patch. The
logarithmic threshold is uniform in the scale, time and real center. -/
theorem output_full_ball_geometry (d : ℕ) :
    ∃ L₀ : ℝ, 10000 ≤ L₀ ∧ ∀ (h L : ℝ) (τ : ℂ), 0 < h → L₀ ≤ L →
      h * L ≤ ‖τ‖ → ‖τ‖ ≤ 4 * (h * L) →
      ∀ (y : OAI.Analysis.Calculus.Current.SpatialSpace d) (u : Option (Fin d) → ℂ),
      u ∈ outputParameterPatch d (Real.sqrt L)⁻¹ →
      ∀ x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3,
      ‖x - spatialPacketEmbedding d y (OAI.Analysis.Calculus.Current.physicalFiberInverse (h * L) τ u)‖ ≤ h →
      spatialDefiningFunction d (h * L) τ x < 0 ∧
      OAI.Analysis.Calculus.Current.physicalEmbedding τ (OAI.Analysis.PDE.Green.physicalSpatialProjection d x) none ≠ 0 ∧
      ‖OAI.Analysis.Calculus.Current.phi (OAI.Analysis.Calculus.Current.physicalEmbedding τ (OAI.Analysis.PDE.Green.physicalSpatialProjection d x)) / (h * L : ℝ)‖ ≤ 1 / 100 ∧
      ‖transverseRatio (OAI.Analysis.Calculus.Current.physicalEmbedding τ (OAI.Analysis.PDE.Green.physicalSpatialProjection d x))‖ ≤ 2 * (Real.sqrt L)⁻¹ := by
  obtain ⟨δ, C, hδ, hC, hlip⟩ := physical_coordinates_lipschitz d
  let D : ℝ := ‖OAI.Analysis.PDE.Green.physicalSpatialProjection d‖ + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  obtain ⟨L₀, hL₀, hth⟩ := output_log_threshold d hδ hC hD
  refine ⟨L₀, hL₀, ?_⟩
  intro h L τ hh hL ht ht' y u hu x hx
  obtain ⟨hL0, hγ1, hDδ, hCD⟩ := hth L hL
  have ha : 0 < h * L := mul_pos hh hL0
  have hγ : 0 ≤ (Real.sqrt L)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg L)
  have hup : u ∈ OAI.Analysis.Calculus.Current.fiberParameterBall d := OAI.Analysis.PDE.Green.openFiberParameterBall_subset d
    (outputParameterPatch_subset hγ hγ1 hu)
  let center := spatialPacketEmbedding d y (OAI.Analysis.Calculus.Current.physicalFiberInverse (h * L) τ u)
  have hq : ‖OAI.Analysis.PDE.Green.physicalSpatialProjection d x - OAI.Analysis.Calculus.Current.physicalFiberInverse (h * L) τ u‖ ≤ D * h := by
    have he := (OAI.Analysis.PDE.Green.physicalSpatialProjection d).le_opNorm (x - center)
    rw [map_sub, spatialPacketEmbedding_projection] at he
    have hmul := mul_le_mul_of_nonneg_left hx (norm_nonneg (OAI.Analysis.PDE.Green.physicalSpatialProjection d))
    apply (he.trans hmul).trans
    dsimp only [D]
    nlinarith
  have hqδ : ‖OAI.Analysis.PDE.Green.physicalSpatialProjection d x - OAI.Analysis.Calculus.Current.physicalFiberInverse (h * L) τ u‖ ≤ h * L * δ :=
    hq.trans (by nlinarith)
  have hcoord := hlip (h * L) τ u (OAI.Analysis.PDE.Green.physicalSpatialProjection d x) ha ht ht' hup hqδ
  have hdiff : ‖OAI.Analysis.Calculus.Current.physicalFiberCoordinates (h * L) τ (OAI.Analysis.PDE.Green.physicalSpatialProjection d x) - u‖ ≤
      (Real.sqrt L)⁻¹ / (4 * ((d : ℝ) + 1)) := by
    apply hcoord.2.trans
    calc
      _ ≤ (C / (h * L)) * (D * h) :=
        mul_le_mul_of_nonneg_left hq (div_nonneg hC.le ha.le)
      _ = C * D / L := by field_simp
      _ ≤ _ := hCD
  have hs := outputParameterPatch_stable hγ hγ1 hu hdiff
  refine ⟨?_, hcoord.1, hs.1, ?_⟩
  · change OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) (h * L) τ (OAI.Analysis.PDE.Green.physicalSpatialProjection d x) < 0
    rw [OAI.Analysis.PDE.Green.physical_defining_coordinates]
    have hp := hs.2.2
    change (∑ i, ‖OAI.Analysis.Calculus.Current.physicalFiberCoordinates (h * L) τ (OAI.Analysis.PDE.Green.physicalSpatialProjection d x) i‖ ^ 2) <
      (1 / 100 : ℝ) at hp
    linarith
  · have he : ‖transverseRatio (OAI.Analysis.Calculus.Current.physicalEmbedding τ (OAI.Analysis.PDE.Green.physicalSpatialProjection d x))‖ ^ 2 =
        ∑ i, ‖OAI.Analysis.Calculus.Current.ratio (OAI.Analysis.Calculus.Current.physicalEmbedding τ (OAI.Analysis.PDE.Green.physicalSpatialProjection d x)) i‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      rfl
    have ht := hs.2.1
    change (∑ i, ‖OAI.Analysis.Calculus.Current.ratio (OAI.Analysis.Calculus.Current.physicalEmbedding τ (OAI.Analysis.PDE.Green.physicalSpatialProjection d x)) i‖ ^ 2) ≤
      4 * (Real.sqrt L)⁻¹ ^ 2 at ht
    nlinarith [norm_nonneg (transverseRatio (OAI.Analysis.Calculus.Current.physicalEmbedding τ (OAI.Analysis.PDE.Green.physicalSpatialProjection d x)))]

end OAI.Analysis.PDE.Concentration
