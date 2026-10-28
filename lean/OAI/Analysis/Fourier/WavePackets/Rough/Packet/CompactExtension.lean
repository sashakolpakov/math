import OAI.Analysis.Fourier.WavePackets.Rough.Packet.Transport
import OAI.Analysis.Calculus.SmoothExtension.Periodic.Infinity
import OAI.Analysis.PDE.Concentration.Packet.LocalRegularity

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module Metric OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.Analysis.Calculus.SmoothExtension
open scoped Topology ContDiff

variable {d : ℕ} {ι : Type*} [Fintype ι] {a : ℝ}
  {b : Basis ι ℝ ((Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ))}
  {B F : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 → ℝ}
local notation "T" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4

/-- On every compact band inside the physical annulus, local joint smooth
representatives glue to one global smooth, spatially periodic function.
This does not assert extension across the annulus endpoints. -/
theorem PaddedSolutionFamily.smooth_extension_on_compact_parameters
    (S : PaddedSolutionFamily d a b B F) (ha : 0 < a)
    (hl : ∀ p : T × E, p.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a →
      paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2 ≤ 0 →
      ∃ O : Set (T × E), IsOpen O ∧ p ∈ O ∧
        ∃ u : T × E → ℝ, ContDiffOn ℝ ∞ u O ∧
          ∀ q ∈ O, q.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a →
            paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime q.1) q.2 ≤ 0 →
            u q = S.physicalValue q)
    {A : Set T} (hA : IsCompact A) (hAann : A ⊆ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a) :
    ∃ u : T × E → ℝ, ContDiff ℝ ∞ u ∧
      (∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit d) b (fun x => u (z,x))) ∧
      ∀ p : T × E, p.1 ∈ A →
        paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2 ≤ 0 →
        u p = S.physicalValue p := by
  let e := parameterLatticeSplit (Z := T) (paddedPhysicalSplit d)
  let C := OAI.Analysis.PDE.Concentration.packetCompactTransverse d a A
  let K : Set (T × E) :=
    {p | p.1 ∈ A ∧ paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2 ≤ 0}
  have hC : IsCompact C :=
    OAI.Analysis.PDE.Concentration.isCompact_packetCompactTransverse d a ha hA (fun z hz => (hAann hz).1.le)
  have hK : IsClosed K := by
    change IsClosed ((fun p : T × E => (e p).2) ⁻¹' C)
    exact hC.isClosed.preimage (continuous_snd.comp e.continuous)
  let C' := e.symm '' (parallelepiped b ×ˢ C)
  have hC' : IsCompact C' :=
    (b.parallelepiped.isCompact.prod hC).image e.symm.continuous
  have hKper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b (fun p => p ∈ K) := by
    intro p l
    change ((e (e.symm ((e p).1 + (l : _),(e p).2))).2 ∈ C) = ((e p).2 ∈ C)
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hrep : ∀ p ∈ K, OAI.Analysis.PDE.Dirichlet.latticeRepresentative e b p ∈ C' := by
    intro p hp
    refine ⟨(ZSpan.fract b (e p).1,(e p).2),⟨?_,hp⟩,rfl⟩
    exact ZSpan.fundamentalDomain_subset_parallelepiped b
      (ZSpan.fract_mem_fundamentalDomain b (e p).1)
  have hper : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b S.physicalValue :=
    (parameter_latticePeriodic_iff (paddedPhysicalSplit d) b S.physicalValue).mpr
      S.physicalValue_periodic
  obtain ⟨u,hu,hup,hue⟩ := OAI.Analysis.Calculus.SmoothExtension.exists_latticePeriodic_smooth_extension_of_local_on
    e b hK hC' hKper hrep S.physicalValue hper (by
      intro p hp
      obtain ⟨O,hO,hpO,g,hg,hge⟩ := hl p (hAann hp.1) hp.2
      exact ⟨O,hO,hpO,g,hg,fun q hq => hge q hq.2 (hAann hq.1.1) hq.1.2⟩)
  exact ⟨u,hu,(parameter_latticePeriodic_iff (paddedPhysicalSplit d) b u).mp hup,
    fun p hp hx => hue p ⟨hp,hx⟩⟩

end OAI.Analysis.Fourier.WavePackets
