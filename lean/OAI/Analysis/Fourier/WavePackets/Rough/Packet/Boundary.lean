import OAI.Analysis.PDE.Dirichlet.Rough.Joint.PhysicalChart
import OAI.Analysis.PDE.Elliptic.Calculus.JointBoundaryChart
import OAI.Analysis.Fourier.WavePackets.Packet.JointFamily
import OAI.Analysis.Fourier.WavePackets.Packet.Equation
import OAI.Analysis.Fourier.WavePackets.Rough.Packet.Interior
import OAI.Analysis.Fourier.WavePackets.Rough.Packet.Transport

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module Metric OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open OAI.Analysis.PDE.Dirichlet.ParameterDeformation
open scoped Topology ContDiff ComplexOrder Matrix.Norms.Elementwise

variable {n : ℕ} {ι : Type*} [Fintype ι]
  {R : OAI.Analysis.Calculus.Current.SpatialSpace (n+1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n+1)}
  {h a : ℝ} {ha : 0 < a} {κ cR cI : ι → ℝ} {v : ι → Fin (n+1) → ℝ} {lam : ℝ}
local notation "PT" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3
local notation "PE" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n+2) 4
local notation "PX" => EuclideanSpace ℝ (Fin ((n+2)*4))
local notation "e" => paddedPhysicalSplit (n+1)
local notation "b" => paddedLatticeBasis (m := n+2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)

/-- A genuine joint smooth representative at each point of a moving
packet boundary. The combined implicit families, the actual classical
fiber equations, and normal-symbol positivity discharge all regularity
inputs of the half-space bootstrap. -/
theorem PaddedSolutionFamily.referenceValue_local_boundary
    (S : PaddedSolutionFamily (n+1) a b
      (packetPaddedBackground n a ha lam) (packetPaddedSource R h a ha κ cR cI v lam))
    (hh : 0 < h)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n+1) j) 1)) = (l:ℝ)*(2*Real.pi)/100)
    {z₀ : PT} (hz₀ : z₀ ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a) {x₀ : PE}
    (hx₀ : paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x₀ = 0) :
    ∃ O : Set (PT × PE), IsOpen O ∧ (z₀,x₀) ∈ O ∧
      ∃ g : PT × PE → ℝ, ContDiff ℝ ∞ g ∧
        ∀ p ∈ O, paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) p.2 ≤ 0 →
          g p = S.referenceValue z₀ p := by
  let D := S.data z₀
  have hDphysical : PaddedPhysicalDataAt a z₀
      (packetPaddedBackground n a ha lam) (packetPaddedSource R h a ha κ cR cI v lam) D :=
    S.physical z₀ hz₀
  have hDx : D.defining x₀ = 0 := (hDphysical.defining_eq hx₀.le).trans hx₀
  obtain ⟨δ,hδ,hδsub⟩ := Metric.mem_nhds_iff.mp ((OAI.Analysis.PDE.Concentration.isOpen_physicalEnergyAnnulus a).mem_nhds hz₀)
  let ρ := δ / 2
  have hρ : 0 < ρ := half_pos hδ
  have hC : closedBall z₀ ρ ⊆ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a :=
    (closedBall_subset_ball (show ρ < δ by dsimp [ρ]; linarith)).trans hδsub
  obtain ⟨A⟩ := nonempty_packetSmoothCoefficients R h a hh ha κ cR cI v hfreq lam z₀ hz₀.1.le
    (isCompact_closedBall z₀ ρ) (fun z hz => (hC hz).1.le)
  let j : PX ≃ₗᵢ[ℝ] PE := (OAI.Analysis.PDE.Dirichlet.flattenFourSlots (n+2)).symm
  let k : Fin ((n+2)*4) := ⟨0,by omega⟩
  obtain ⟨c,G,P,hc,hG,hP,hG0,hP0,hchart,V,hV,hxV,hGPV,hPV⟩ :=
    OAI.Analysis.PDE.Elliptic.exists_joint_boundary_chart j k D.defining_smooth x₀ hDx (D.regular x₀ hDx)
  let hΩK : {x : PE | D.defining x < 0} ⊆ {x | D.defining x ≤ 0} :=
    fun x hx => show D.defining x ≤ 0 from le_of_lt hx
  have hbase : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.HasJointGeometricSolutionFamiliesAt (T := PE) e b D.defining
      (S.referenceValue z₀) hΩK (1/2) z₀ :=
    S.hasJointGeometricSolutionFamiliesAt hh hfreq hz₀ (by norm_num) (by norm_num) hΩK
  have htangent : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.HasJointGeometricSolutionFamiliesAt
      (T := (EuclideanSpace.proj k : PX →L[ℝ] ℝ).ker) e b D.defining
      (S.referenceValue z₀) hΩK (1/2) z₀ :=
    S.hasJointGeometricSolutionFamiliesAt hh hfreq hz₀ (by norm_num) (by norm_num) hΩK
  obtain ⟨O,hO,hxO,g,hg,hge⟩ := OAI.Analysis.PDE.Dirichlet.ParameterDeformation.exists_smooth_joint_physical_chart e b D.defining
    D.defining_smooth D.defining_periodic D.regular D.closed_subset_closure hΩK (1/2)
    (S.referenceValue z₀) isOpen_ball (mem_ball_self hρ) hbase
    (fun z hz x hx => S.referenceValue_joint_contDiffAt_interior hh hfreq hz₀
      (hC (ball_subset_closedBall hz)) ((hDphysical.interior x).mp hx))
    j G P hG hP (EuclideanSpace.proj k) (EuclideanSpace.single k 1) (by simp)
    hc (fun x hx => (hchart x hx).2.2) (fun x hx => (hchart x hx).1)
    (fun x hx => (hchart x hx).2.1) htangent
    (fun z hz x hx => (S.referenceValue_slice_smooth ha hz₀.1.le z
      ((hDphysical.closed x).mp hx)).of_le (by simp))
    A.background A.jacobian A.curvature A.source
    A.background_smooth A.jacobian_smooth A.curvature_smooth A.source_smooth
    (fun z hz x hx => A.jacobian_surjective hz₀.1.le (ball_subset_closedBall hz)
      (hC (ball_subset_closedBall hz)).1.le ((hDphysical.closed x).mp hx))
    (fun z hz x hx => A.referenceValue_positive S hz₀.1.le (ball_subset_closedBall hz)
      (hC (ball_subset_closedBall hz)) ((hDphysical.closed x).mp hx))
    (fun z hz x hx => A.referenceValue_equation S hz₀.1.le (ball_subset_closedBall hz)
      (hC (ball_subset_closedBall hz)) ((hDphysical.closed x).mp hx))
    hP0 hV hxV hGPV hPV
  exact ⟨O,hO,hxO,g,hg,fun p hp hx => hge p hp ((hDphysical.closed p.2).mpr hx)⟩

theorem PaddedSolutionFamily.local_physical_boundary_representative
    (S : PaddedSolutionFamily (n+1) a b
      (packetPaddedBackground n a ha lam) (packetPaddedSource R h a ha κ cR cI v lam))
    (hh : 0 < h)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n+1) j) 1)) = (l:ℝ)*(2*Real.pi)/100)
    {z₀ : PT} (hz₀ : z₀ ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a) {x₀ : PE}
    (hx₀ : paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x₀ = 0) :
    ∃ O : Set (PT × PE), IsOpen O ∧ (z₀,x₀) ∈ O ∧
      ∃ g : PT × PE → ℝ, ContDiffOn ℝ ∞ g O ∧
        ∀ p ∈ O, p.1 ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a →
          paddedPhysicalDefining (n+1) a (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2 ≤ 0 →
          g p = S.physicalValue p := by
  obtain ⟨O,hO,hxO,g,hg,hge⟩ := S.referenceValue_local_boundary hh hfreq hz₀ hx₀
  exact S.local_physical_representative ha hz₀ hx₀.le hO hxO hg.contDiffOn
    (fun p hp _ hx => hge p hp hx)

end OAI.Analysis.Fourier.WavePackets
