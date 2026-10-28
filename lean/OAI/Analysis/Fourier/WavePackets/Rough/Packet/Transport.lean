import OAI.Analysis.Fourier.WavePackets.Rough.Packet.Family

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module Metric OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology ContDiff

variable {d : ℕ} {ι : Type*} [Fintype ι] {a : ℝ}
  {b : Basis ι ℝ ((Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ))}
  {B F : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 → ℝ}
local notation "T" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4

/-- Local smooth reference-fiber representatives give local smooth
representatives in the original moving physical coordinates, including
the boundary. The chart is used only on its genuine regular domain. -/
theorem PaddedSolutionFamily.local_physical_representative
    (S : PaddedSolutionFamily d a b B F) (ha : 0 < a)
    {z₀ : T} (hz₀ : z₀ ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a) {x₀ : E}
    (hx₀ : paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x₀ ≤ 0)
    {O : Set (T × E)} (hO : IsOpen O) (hxO : (z₀,x₀) ∈ O)
    {g : T × E → ℝ} (hg : ContDiffOn ℝ ∞ g O)
    (he : ∀ p ∈ O, p.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a →
      paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) p.2 ≤ 0 →
      g p = S.referenceValue z₀ p) :
    ∃ V : Set (T × E), IsOpen V ∧ (z₀,x₀) ∈ V ∧
      ∃ u : T × E → ℝ, ContDiffOn ℝ ∞ u V ∧
        ∀ p ∈ V, p.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a →
          paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2 ≤ 0 →
          u p = S.physicalValue p := by
  let H : T × E → T × E := fun p =>
    (p.1,paddedPhysicalTransport d a (OAI.Analysis.PDE.Green.energyComplexTime p.1) (OAI.Analysis.PDE.Green.energyComplexTime z₀) p.2)
  let R : Set (T × E) :=
    {p | (paddedPhysicalSplit d p.2).2 ∈ OAI.Analysis.Calculus.Current.physicalRegularDomain (OAI.Analysis.PDE.Green.energyComplexTime p.1)}
  have hR : IsOpen R :=
    (isOpen_jointPhysicalRegular d).preimage
      (((OAI.Analysis.PDE.Green.contDiff_energyComplexTime ∞).continuous.comp continuous_fst).prodMk
        (continuous_snd.comp ((paddedPhysicalSplit d).continuous.comp continuous_snd)))
  have hH : ∀ p ∈ R, ContDiffAt ℝ ∞ H p := by
    intro p hp
    have hc : ContDiff ℝ ∞ (fun q : T × E => (OAI.Analysis.PDE.Green.energyComplexTime q.1,q.2)) :=
      ((OAI.Analysis.PDE.Green.contDiff_energyComplexTime ∞).comp contDiff_fst).prodMk contDiff_snd
    have hcomp := (contDiffAt_paddedPhysicalTransport_reverse_regular d a
      (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime p.1) hp).comp p hc.contDiffAt
    exact contDiffAt_fst.prodMk hcomp
  let V : Set (T × E) := R ∩ H ⁻¹' O
  have hV : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    exact inter_mem (hR.mem_nhds hp.1)
      ((hH p hp.1).continuousAt.preimage_mem_nhds (hO.mem_nhds hp.2))
  have hxR : (z₀,x₀) ∈ R :=
    OAI.Analysis.Calculus.Current.physical_fiber_collar_subset_regular a (OAI.Analysis.PDE.Green.energyComplexTime z₀) ha hz₀.1.le
      (hx₀.trans (by norm_num : (0 : ℝ) ≤ 1))
  have hxH : H (z₀,x₀) = (z₀,x₀) := by
    dsimp only [H]
    rw [paddedPhysicalTransport_self d a _ ha hz₀.1.le hx₀]
  refine ⟨V,hV,⟨hxR,by simpa only [mem_preimage,hxH] using hxO⟩,
    g ∘ H,?_,?_⟩
  · exact hg.comp (fun p hp => (hH p hp.1).contDiffWithinAt) (fun p hp => hp.2)
  · intro p hp hpz hpx
    have href : paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) (H p).2 ≤ 0 :=
      (paddedPhysicalTransport_defining d a (OAI.Analysis.PDE.Green.energyComplexTime p.1)
        (OAI.Analysis.PDE.Green.energyComplexTime z₀) ha hz₀.1.le hpx).trans_le hpx
    exact (he (H p) hp.2 hpz href).trans
      (S.referenceValue_inverse ha hz₀.1.le hpz.1.le hpx)

end OAI.Analysis.Fourier.WavePackets
