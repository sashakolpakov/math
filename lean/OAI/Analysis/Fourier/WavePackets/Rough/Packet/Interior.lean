import OAI.Analysis.Fourier.WavePackets.Packet.JointFamily
import OAI.Analysis.Fourier.WavePackets.FamilyHessianContinuity

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open OAI.Analysis.PDE.Dirichlet.ParameterDeformation
open scoped Topology ContDiff

variable {n : ℕ} {ι : Type*} [Fintype ι]
  {R : OAI.Analysis.Calculus.Current.SpatialSpace (n+1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n+1)}
  {h a : ℝ} {ha : 0 < a} {κ cR cI : ι → ℝ} {v : ι → Fin (n+1) → ℝ} {lam : ℝ}
local notation "PT" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3
local notation "PE" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n+2) 4
variable (S : PaddedSolutionFamily (n+1) a
  (paddedLatticeBasis (m := n+2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R))
  (packetPaddedBackground n a ha lam) (packetPaddedSource R h a ha κ cR cI v lam))
  (hh : 0 < h)
  (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
    (R (EuclideanSpace.single (finSuccEquiv (n+1) j) 1)) = (l:ℝ)*(2*Real.pi)/100)
include hh hfreq

/-- At its reference parameter, the genuine family is jointly smooth
at every strictly interior spatial point. -/
theorem PaddedSolutionFamily.referenceValue_joint_contDiffAt_self
    {z : PT} (hz : z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a) {x : PE}
    (hx : paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime z) x < 0) :
    ContDiffAt ℝ ∞ (S.referenceValue z) (z,x) := by
  have hΩK : {y | (S.data z).defining y < 0} ⊆ {y | (S.data z).defining y ≤ 0} := by
    intro y hy
    exact show (S.data z).defining y ≤ 0 from (show (S.data z).defining y < 0 from hy).le
  have hc := S.hasJointGeometricSolutionFamiliesAt (T := PE) hh hfreq hz
    (α := 1/2) (by norm_num) (by norm_num) hΩK
  exact hc.joint_contDiffAt_interior (S.data z).defining_smooth.continuous
    (S.data z).defining_periodic (((S.physical z hz).interior x).mpr hx)

/-- Moving back by the actual inverse fiber map gives joint smoothness
of the chosen physical solution on the moving strict interior. -/
theorem PaddedSolutionFamily.physicalValue_joint_contDiffAt_interior
    {z : PT} (hz : z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a) {x : PE}
    (hx : paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime z) x < 0) :
    ContDiffAt ℝ ∞ S.physicalValue (z,x) := by
  let H : PT × PE → PT × PE := fun p =>
    (p.1,paddedPhysicalTransport (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime p.1) (OAI.Analysis.PDE.Green.energyComplexTime z) p.2)
  have hc : ContDiff ℝ ∞ (fun p : PT × PE => (OAI.Analysis.PDE.Green.energyComplexTime p.1,p.2)) :=
    ((OAI.Analysis.PDE.Green.contDiff_energyComplexTime ∞).comp contDiff_fst).prodMk contDiff_snd
  have hcomp := (contDiffAt_paddedPhysicalTransport_reverse_joint (n+1) a
    (OAI.Analysis.PDE.Green.energyComplexTime z) (OAI.Analysis.PDE.Green.energyComplexTime z) ha hz.1.le hx.le).comp (z,x) hc.contDiffAt
  have hH : ContDiffAt ℝ ∞ H (z,x) := contDiffAt_fst.prodMk hcomp
  have hHself : H (z,x) = (z,x) := by
    dsimp only [H]
    rw [paddedPhysicalTransport_self (n+1) a _ ha hz.1.le hx.le]
  have hs : ContDiffAt ℝ ∞ (S.referenceValue z) (H (z,x)) := by
    rw [hHself]
    exact S.referenceValue_joint_contDiffAt_self hh hfreq hz hx
  apply (hs.comp (z,x) hH).congr_of_eventuallyEq
  have hnear : ∀ᶠ p : PT × PE in 𝓝 (z,x),
      paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2 < 0 :=
    (contDiffAt_paddedPhysicalDefining_joint (n+1) a ha (z,x) hz.1.le hx.le).continuousAt
      |>.eventually_lt continuousAt_const hx
  have hznear : ∀ᶠ p : PT × PE in 𝓝 (z,x), p.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a :=
    continuous_fst.continuousAt.preimage_mem_nhds (OAI.Analysis.PDE.Concentration.isOpen_physicalEnergyAnnulus a |>.mem_nhds hz)
  filter_upwards [hnear,hznear] with p hp hpz
  exact (S.referenceValue_inverse ha hz.1.le hpz.1.le hp.le).symm

/-- Joint interior smoothness holds in any fixed reference fiber, not
only when its reference parameter is the current parameter. -/
theorem PaddedSolutionFamily.referenceValue_joint_contDiffAt_interior
    {z₀ z : PT} (hz₀ : z₀ ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a) (hz : z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a)
    {x : PE} (hx : paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x < 0) :
    ContDiffAt ℝ ∞ (S.referenceValue z₀) (z,x) := by
  let y := paddedPhysicalTransport (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime z) x
  have hy : paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0 := by
    dsimp only [y]
    rwa [paddedPhysicalTransport_defining (n+1) a _ _ ha hz.1.le hx.le]
  have hc : ContDiff ℝ ∞ (fun p : PT × PE => (OAI.Analysis.PDE.Green.energyComplexTime p.1,p.2)) :=
    ((OAI.Analysis.PDE.Green.contDiff_energyComplexTime ∞).comp contDiff_fst).prodMk contDiff_snd
  have hcomp := (contDiffAt_paddedPhysicalTransport_joint (n+1) a
    (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime z) ha hz₀.1.le hx.le).comp (z,x) hc.contDiffAt
  have hH : ContDiffAt ℝ ∞ (fun p : PT × PE =>
      (p.1,paddedPhysicalTransport (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2))
      (z,x) := contDiffAt_fst.prodMk hcomp
  exact (S.physicalValue_joint_contDiffAt_interior hh hfreq hz hy).comp (z,x) hH

/-- The moving strict interior is an actual open region of joint smoothness. -/
theorem PaddedSolutionFamily.local_physical_interior_representative
    {z : PT} (hz : z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a) {x : PE}
    (hx : paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime z) x < 0) :
    ∃ O : Set (PT × PE), IsOpen O ∧ (z,x) ∈ O ∧
      ∃ g : PT × PE → ℝ, ContDiffOn ℝ ∞ g O ∧
        ∀ p ∈ O, p.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a →
          paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2 ≤ 0 →
          g p = S.physicalValue p := by
  let O : Set (PT × PE) := {p | p.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ∧
    paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2 < 0}
  have hO : IsOpen O := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    have hpn : ∀ᶠ q : PT × PE in 𝓝 p, q.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a :=
      continuous_fst.continuousAt.preimage_mem_nhds
        ((OAI.Analysis.PDE.Concentration.isOpen_physicalEnergyAnnulus a).mem_nhds hp.1)
    have hqn : ∀ᶠ q : PT × PE in 𝓝 p,
        paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime q.1) q.2 < 0 :=
      (contDiffAt_paddedPhysicalDefining_joint (n+1) a ha p hp.1.1.le hp.2.le).continuousAt
        |>.eventually_lt continuousAt_const hp.2
    exact hpn.and hqn
  refine ⟨O,hO,⟨hz,hx⟩,S.physicalValue,?_,?_⟩
  · intro p hp
    exact (S.physicalValue_joint_contDiffAt_interior hh hfreq hp.1 hp.2).contDiffWithinAt
  · intro p hp hpz hpx
    rfl

end OAI.Analysis.Fourier.WavePackets
