import OAI.Analysis.Fourier.WavePackets.Rough.Packet.CompactExtension
import OAI.Analysis.Calculus.SmoothExtension.SpatialPeriodicBands

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.Analysis.Calculus.SmoothExtension
open scoped Topology ContDiff

variable {d : ℕ} {ι : Type*} [Fintype ι] {a : ℝ}
  {b : Basis ι ℝ ((Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ))}
  {B F : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 → ℝ}
local notation "T" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4

/-- Joint local regularity supplies one periodic smooth representative on
the open annulus, agreeing with every chosen fiber solution. Nothing is
claimed at either degenerate parameter endpoint. -/
theorem PaddedSolutionFamily.smooth_representative_on_annulus
    (S : PaddedSolutionFamily d a b B F) (ha : 0 < a)
    (hl : ∀ p : T × E, p.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a →
      paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2 ≤ 0 →
      ∃ O : Set (T × E), IsOpen O ∧ p ∈ O ∧
        ∃ u : T × E → ℝ, ContDiffOn ℝ ∞ u O ∧
          ∀ q ∈ O, q.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a →
            paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime q.1) q.2 ≤ 0 →
            u q = S.physicalValue q) :
    ∃ u : T × E → ℝ, ContDiffOn ℝ ∞ u (OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ×ˢ univ) ∧
      (∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit d) b (fun x => u (z,x))) ∧
      ∀ p : T × E, p.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a →
        paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2 ≤ 0 →
        u p = S.physicalValue p := by
  let K : Set (T × E) :=
    {p | paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2 ≤ 0}
  obtain ⟨u,hu,hup,hue⟩ := OAI.Analysis.Calculus.SmoothExtension.exists_spatially_periodic_smooth_on_of_compact_bands
    (paddedPhysicalSplit d) b (OAI.Analysis.PDE.Concentration.isOpen_physicalEnergyAnnulus a) K S.physicalValue (by
      intro C hC hCsub
      obtain ⟨g,hg,hgp,hge⟩ := S.smooth_extension_on_compact_parameters ha hl hC hCsub
      exact ⟨g,hg,hgp,fun p hp hpC => hge p hpC hp⟩)
  exact ⟨u,hu,hup,fun p hp hx => hue p hx hp⟩

end OAI.Analysis.Fourier.WavePackets
