import OAI.Analysis.Fourier.WavePackets.TransportExtension
import OAI.Analysis.Fourier.WavePackets.Dirichlet.Descent

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology ContDiff

variable {F ι : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι]

def pullPhysicalCoefficient (d : ℕ) (a : ℝ) (z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 → F)
    (p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4) : F :=
  f (p.1, paddedPhysicalTransport d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2)

omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem latticePeriodic_comp_paddedPhysicalTransport (d : ℕ) (a : ℝ) (τ₀ τ : ℂ)
    (b : Basis ι ℝ ((Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ)))
    {f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 → F} (hf : OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit d) b f) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit d) b (fun x => f (paddedPhysicalTransport d a τ₀ τ x)) := by
  apply OAI.Analysis.PDE.Concentration.latticePeriodic_of_basis_periods
  intro i x
  change f (paddedPhysicalTransport d a τ₀ τ (x + (paddedPhysicalSplit d).symm (b i,0))) =
    f (paddedPhysicalTransport d a τ₀ τ x)
  rw [paddedPhysicalTransport_add]
  exact latticePeriodic_basis_add (paddedPhysicalSplit d) b hf i _

/-- A globally smooth periodic physical coefficient pulled to the base
fiber has a globally smooth periodic extension near every compact set of
parameters and all closed base-fiber points. -/
theorem exists_pullPhysicalCoefficient_extension [FiniteDimensional ℝ F]
    (d : ℕ) (a : ℝ) (z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (ha : 0 < a) (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖)
    (b : Basis ι ℝ ((Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ)))
    {T : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)} (hT : IsCompact T)
    (f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 → F)
    (hf : ContDiff ℝ ∞ f)
    (hfp : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit d) b (fun x => f (z,x))) :
    ∃ g : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 → F,
      ContDiff ℝ ∞ g ∧ (∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit d) b (fun x => g (z,x))) ∧
      ∀ z ∈ T, ∀ x, paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0 →
        g =ᶠ[𝓝 (z,x)] pullPhysicalCoefficient d a z₀ f := by
  let C : Set (Option (Fin d) → ℂ) :=
    {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) q ≤ 0}
  have hC : IsCompact C := OAI.Analysis.Calculus.Current.isCompact_physical_fiber_sublevel a (OAI.Analysis.PDE.Green.energyComplexTime z₀) ha hz₀ 0 (by norm_num)
  let U : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4) :=
    {p | (paddedPhysicalSplit d p.2).2 ∈ OAI.Analysis.Calculus.Current.physicalRegularDomain (OAI.Analysis.PDE.Green.energyComplexTime z₀)}
  have hU : IsOpen U := (OAI.Analysis.Calculus.Current.isOpen_physicalRegularDomain (OAI.Analysis.PDE.Green.energyComplexTime z₀)).preimage (by fun_prop)
  have hCU (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (_ : z ∈ T) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4)
      (hx : (paddedPhysicalSplit d x).2 ∈ C) : (z,x) ∈ U :=
    OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a (OAI.Analysis.PDE.Green.energyComplexTime z₀) ha hz₀
      (hx.trans (show (0 : ℝ) ≤ 1 by norm_num))
  have hcomp : ContDiffOn ℝ ∞ (pullPhysicalCoefficient d a z₀ f) U := by
    intro p hp
    have hc : ContDiff ℝ ∞ (fun p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 =>
        (OAI.Analysis.PDE.Green.energyComplexTime p.1,p.2)) :=
      ((OAI.Analysis.PDE.Green.contDiff_energyComplexTime ∞).comp contDiff_fst).prodMk contDiff_snd
    have hΦ := (contDiffAt_paddedPhysicalTransport_regular d a (OAI.Analysis.PDE.Green.energyComplexTime z₀)
      (OAI.Analysis.PDE.Green.energyComplexTime p.1) hp).comp p hc.contDiffAt
    exact (hf.contDiffAt.comp p (contDiffAt_fst.prodMk hΦ)).contDiffWithinAt
  exact exists_smooth_parameter_lattice_extension (paddedPhysicalSplit d) b hT hC hU hCU
    (pullPhysicalCoefficient d a z₀ f) hcomp
    (fun z => latticePeriodic_comp_paddedPhysicalTransport d a (OAI.Analysis.PDE.Green.energyComplexTime z₀)
      (OAI.Analysis.PDE.Green.energyComplexTime z) b (hfp z))

end OAI.Analysis.Fourier.WavePackets
