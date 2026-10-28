import OAI.Analysis.Fourier.WavePackets.TransportRegular
import OAI.Analysis.Fourier.WavePackets.ParameterExtension

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology ContDiff

def packetTransportJ (d : ℕ) (a : ℝ) (z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4) :=
  physicalTransportJ d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime p.1,p.2)

def packetTransportK (d : ℕ) (a : ℝ) (z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (p : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4) :=
  physicalTransportK d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime p.1,p.2)

/-- Actual globally smooth periodic extensions of the moving-fiber
Jacobian and second derivative, equal as joint germs along all base-fiber
points and compact admissible parameters. -/
theorem exists_packetTransport_extensions (d : ℕ) (a : ℝ)
    (z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (ha : 0 < a) (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖)
    {ι : Type*} [Fintype ι]
    (b : Basis ι ℝ ((Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ)))
    {T : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)} (hT : IsCompact T)
    (hTreg : ∀ z ∈ T, a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) :
    ∃ (J : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 →
        OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4)
      (K : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 →
        OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4),
      ContDiff ℝ ∞ J ∧ ContDiff ℝ ∞ K ∧
      (∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit d) b (fun x => J (z,x))) ∧
      (∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit d) b (fun x => K (z,x))) ∧
      ∀ z ∈ T, ∀ x, paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0 →
        J =ᶠ[𝓝 (z,x)] packetTransportJ d a z₀ ∧
        K =ᶠ[𝓝 (z,x)] packetTransportK d a z₀ := by
  let C : Set (Option (Fin d) → ℂ) :=
    {q | OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) q ≤ 0}
  have hC : IsCompact C := OAI.Analysis.Calculus.Current.isCompact_physical_fiber_sublevel a (OAI.Analysis.PDE.Green.energyComplexTime z₀) ha hz₀ 0 (by norm_num)
  let Ψ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 → ℂ × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 :=
    fun p => (OAI.Analysis.PDE.Green.energyComplexTime p.1,p.2)
  have hΨ : ContDiff ℝ ∞ Ψ := ((OAI.Analysis.PDE.Green.contDiff_energyComplexTime ∞).comp contDiff_fst).prodMk contDiff_snd
  let U := Ψ ⁻¹' transportRegularDomain d a (OAI.Analysis.PDE.Green.energyComplexTime z₀)
  have hU : IsOpen U := (isOpen_transportRegularDomain d a (OAI.Analysis.PDE.Green.energyComplexTime z₀)).preimage hΨ.continuous
  have hCU (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (hz : z ∈ T) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4)
      (hx : (paddedPhysicalSplit d x).2 ∈ C) : (z,x) ∈ U :=
    closedFiber_mem_transportRegularDomain d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime z)
      ha hz₀ (hTreg z hz) hx
  have hJ : ContDiffOn ℝ ∞ (packetTransportJ d a z₀) U :=
    (contDiffOn_physicalTransportJ d a (OAI.Analysis.PDE.Green.energyComplexTime z₀)).comp hΨ.contDiffOn (fun _ hx => hx)
  have hK : ContDiffOn ℝ ∞ (packetTransportK d a z₀) U :=
    (contDiffOn_physicalTransportK d a (OAI.Analysis.PDE.Green.energyComplexTime z₀)).comp hΨ.contDiffOn (fun _ hx => hx)
  have hpJ (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) :
      OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit d) b (fun x => packetTransportJ d a z₀ (z,x)) := by
    apply OAI.Analysis.PDE.Concentration.latticePeriodic_of_basis_periods
    intro i x
    exact physicalTransportJ_add d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime z) x (b i)
  have hpK (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) :
      OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit d) b (fun x => packetTransportK d a z₀ (z,x)) := by
    apply OAI.Analysis.PDE.Concentration.latticePeriodic_of_basis_periods
    intro i x
    exact physicalTransportK_add d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime z) x (b i)
  obtain ⟨J, hJs, hJp, hJe⟩ := exists_smooth_parameter_lattice_extension
    (paddedPhysicalSplit d) b hT hC hU hCU (packetTransportJ d a z₀) hJ hpJ
  obtain ⟨K, hKs, hKp, hKe⟩ := exists_smooth_parameter_lattice_extension
    (paddedPhysicalSplit d) b hT hC hU hCU (packetTransportK d a z₀) hK hpK
  exact ⟨J,K,hJs,hKs,hJp,hKp,fun z hz x hx => ⟨hJe z hz x hx,hKe z hz x hx⟩⟩

end OAI.Analysis.Fourier.WavePackets
