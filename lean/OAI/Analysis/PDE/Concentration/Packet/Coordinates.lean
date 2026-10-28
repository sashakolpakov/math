import OAI.Analysis.PDE.Concentration.Packet.Fiber

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green

/-- Put the physical real spatial vector and complex transverse vector back
into the three-slot coordinates used by the Dirichlet problem. -/
def spatialPacketEmbedding (d : ℕ) (y : OAI.Analysis.Calculus.Current.SpatialSpace d) (q : Option (Fin d) → ℂ) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 3 :=
  OAI.Analysis.PDE.Green.physicalSpatialEmbedding d (fun i => y (finSuccEquiv d i)) q

theorem spatialPacketEmbedding_projection (d : ℕ) (y : OAI.Analysis.Calculus.Current.SpatialSpace d) (q : Option (Fin d) → ℂ) :
    OAI.Analysis.PDE.Green.physicalSpatialProjection d (spatialPacketEmbedding d y q) = q :=
  OAI.Analysis.PDE.Green.physicalSpatialProjection_embedding d _ q

theorem spatialPacketEmbedding_real (d : ℕ) (y : OAI.Analysis.Calculus.Current.SpatialSpace d) (q : Option (Fin d) → ℂ) :
    physicalSpatialRealVector d (spatialPacketEmbedding d y q) = y := by
  ext i
  simp [physicalSpatialRealVector, spatialPacketEmbedding, OAI.Analysis.PDE.Green.physicalSpatialEmbedding_eq,
    OAI.Analysis.PDE.Green.spatialRealComplexEmbedding_apply]

theorem spatialPacketEmbedding_defining (d : ℕ) (a : ℝ) (τ : ℂ)
    (y : OAI.Analysis.Calculus.Current.SpatialSpace d) (q : Option (Fin d) → ℂ) :
    spatialDefiningFunction d a τ (spatialPacketEmbedding d y q) =
      OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q := by
  change OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ (OAI.Analysis.PDE.Green.physicalSpatialProjection d _) = _
  rw [spatialPacketEmbedding_projection]

theorem physicalLatticeCurrent_input_density_embedding {d : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace d ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace d) (h a : ℝ)
    (κ cR cI : ι → ℝ) (v : ι → Fin d → ℝ) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (hz : z (0, 0) = 0) (y : OAI.Analysis.Calculus.Current.SpatialSpace d) (q : Option (Fin d) → ℂ) :
    (physicalLatticeCurrent R h a κ cR cI v
      (OAI.Analysis.PDE.Green.fiberEmbedding (d + 1) 3 z (spatialPacketEmbedding d y q)) 0 0).re =
      OAI.Analysis.Calculus.Current.timeComponent (latticeRegularizedCurrent R h a κ cR cI v
        (0 - nullSpatialShift y) (OAI.Analysis.Calculus.Current.physicalEmbedding (OAI.Analysis.PDE.Green.energyComplexTime z) q)) := by
  rw [physicalLatticeCurrent_input_density R h a κ cR cI v z hz,
    spatialPacketEmbedding_real, spatialPacketEmbedding_projection]

end OAI.Analysis.PDE.Concentration
