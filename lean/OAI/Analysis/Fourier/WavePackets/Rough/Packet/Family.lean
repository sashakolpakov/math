import OAI.Analysis.Fourier.WavePackets.Packet.FamilyBarriers
import OAI.Analysis.Fourier.WavePackets.Dirichlet.Existence
import OAI.Analysis.Fourier.WavePackets.PulledCoefficients
import OAI.Analysis.Fourier.WavePackets.CalculusPacketPushbackGeometry

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module Metric OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology ContDiff

section Data
variable {d : ℕ} {ι : Type*} [Fintype ι]
local notation "T" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4
local notation "P" => (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ)

theorem PaddedPhysicalDataAt.defining_eq
    {a : ℝ} {z : T} {b : Basis ι ℝ P} {B F : T × E → ℝ}
    {D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots (paddedPhysicalSplit d) b}
    (hD : PaddedPhysicalDataAt a z B F D) {x : E}
    (hx : paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ 0) :
    D.defining x = paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z) x :=
  (hD.defining_germ x hx).eq_of_nhds

theorem PaddedPhysicalDataAt.interior
    {a : ℝ} {z : T} {b : Basis ι ℝ P} {B F : T × E → ℝ}
    {D : PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots (paddedPhysicalSplit d) b}
    (hD : PaddedPhysicalDataAt a z B F D) (x : E) :
    D.defining x < 0 ↔ paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z) x < 0 := by
  constructor
  · intro hx
    rwa [hD.defining_eq ((hD.closed x).mp hx.le)] at hx
  · intro hx
    rwa [hD.defining_eq hx.le]

end Data

/-- Independently chosen genuine smooth fiber solutions, together with the
locally uniform barriers inherited from the literal moving-fiber data.
No parameter regularity is included in this structure. -/
structure PaddedSolutionFamily (dim : ℕ) (a : ℝ)
    {ι : Type*} [Fintype ι]
    (b : Basis ι ℝ ((Fin (dim + 1) → ℝ) × (Fin (dim + 1) → ℝ)))
    (B F : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (dim + 1) 4 → ℝ) where
  data : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots (paddedPhysicalSplit dim) b
  solution : ∀ z, PeriodicQuaternionicSolution (data z)
  physical : ∀ z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a, PaddedPhysicalDataAt a z B F (data z)
  barriers : ∀ z₀ ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a,
    ∃ ρ : ℝ, 0 < ρ ∧ closedBall z₀ ρ ⊆ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ∧
      ∃ C c : ℝ, 0 < c ∧ c ≤ C ∧ ∀ z ∈ closedBall z₀ ρ, ∀ x,
        paddedPhysicalDefining dim a (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ 0 →
          C * paddedPhysicalDefining dim a (OAI.Analysis.PDE.Green.energyComplexTime z) x ≤ (solution z).u x ∧
          (solution z).u x ≤ c * paddedPhysicalDefining dim a (OAI.Analysis.PDE.Green.energyComplexTime z) x

namespace PaddedSolutionFamily

variable {d : ℕ} {ι : Type*} [Fintype ι]
local notation "T" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4
local notation "P" => (Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ)

variable {a : ℝ}
  {b : Basis ι ℝ ((Fin (d + 1) → ℝ) × (Fin (d + 1) → ℝ))}
  {B F : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (d + 1) 4 → ℝ}
  (S : PaddedSolutionFamily d a b B F)

/-- The actual chosen solution in physical moving-fiber coordinates. -/
def physicalValue (p : T × E) : ℝ := (S.solution p.1).u p.2

/-- Pull the independently chosen solutions to one fixed reference fiber. -/
def referenceValue (z₀ : T) (p : T × E) : ℝ :=
  (S.solution p.1).u
    (paddedPhysicalTransport d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime p.1) p.2)

theorem physicalValue_periodic (z : T) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit d) b (fun x => S.physicalValue (z,x)) :=
  (S.solution z).periodic

theorem referenceValue_periodic (z₀ z : T) :
    OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit d) b (fun x => S.referenceValue z₀ (z,x)) := by
  let f : E → ℝ := (S.solution z).u
  have hf : OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit d) b f := (S.solution z).periodic
  exact latticePeriodic_comp_paddedPhysicalTransport d a
    (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime z) b (f := f) hf

theorem referenceValue_self (ha : 0 < a) {z₀ : T}
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) {x : E}
    (hx : paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0) :
    S.referenceValue z₀ (z₀,x) = (S.solution z₀).u x := by
  unfold PaddedSolutionFamily.referenceValue
  rw [paddedPhysicalTransport_self d a _ ha hz₀ hx]

theorem referenceValue_slice_smooth (ha : 0 < a) {z₀ : T}
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) (z : T) {x : E}
    (hx : paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0) :
    ContDiffAt ℝ ∞ (fun y => S.referenceValue z₀ (z,y)) x := by
  let f : E → ℝ := (S.solution z).u
  have hf : ContDiff ℝ ∞ f := (S.solution z).smooth
  have hT : ContDiffAt ℝ ∞
      (paddedPhysicalTransport d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime z)) x :=
    contDiffAt_paddedPhysicalTransport_slice d a _ _ ha hz₀ hx
  exact hf.contDiffAt.comp x hT

theorem referenceValue_boundary (ha : 0 < a) (z₀ : T) {z : T}
    (hz : z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a) {x : E}
    (hx : paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x = 0) :
    S.referenceValue z₀ (z,x) = 0 := by
  have he := (paddedPhysicalTransport_defining d a (OAI.Analysis.PDE.Green.energyComplexTime z₀)
    (OAI.Analysis.PDE.Green.energyComplexTime z) ha hz.1.le hx.le).trans hx
  exact (S.solution z).boundary _ (((S.physical z hz).defining_eq he.le).trans he)

theorem referenceValue_inverse (ha : 0 < a) {z₀ z : T}
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) (hz : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖)
    {y : E} (hy : paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0) :
    S.referenceValue z₀
      (z,paddedPhysicalTransport d a (OAI.Analysis.PDE.Green.energyComplexTime z) (OAI.Analysis.PDE.Green.energyComplexTime z₀) y) =
      S.physicalValue (z,y) := by
  unfold PaddedSolutionFamily.referenceValue PaddedSolutionFamily.physicalValue
  rw [paddedPhysicalTransport_inverse d a _ _ ha hz hz₀ hy]

theorem referenceValue_barriers (ha : 0 < a) {z₀ : T}
    (hz₀ : z₀ ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a) :
    ∃ ρ : ℝ, 0 < ρ ∧ closedBall z₀ ρ ⊆ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ∧
      ∃ C c : ℝ, 0 < c ∧ c ≤ C ∧ ∀ z ∈ closedBall z₀ ρ, ∀ x,
        paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0 →
          C * paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤
            S.referenceValue z₀ (z,x) ∧
          S.referenceValue z₀ (z,x) ≤
            c * paddedPhysicalDefining d a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x := by
  obtain ⟨ρ,hρ,hρsub,C,c,hc,hcC,hbound⟩ := S.barriers z₀ hz₀
  refine ⟨ρ,hρ,hρsub,C,c,hc,hcC,?_⟩
  intro z hz x hx
  have he := paddedPhysicalTransport_defining d a (OAI.Analysis.PDE.Green.energyComplexTime z₀)
    (OAI.Analysis.PDE.Green.energyComplexTime z) ha (hρsub hz).1.le hx
  simpa only [he,PaddedSolutionFamily.referenceValue] using
    hbound z hz (paddedPhysicalTransport d a (OAI.Analysis.PDE.Green.energyComplexTime z₀)
      (OAI.Analysis.PDE.Green.energyComplexTime z) x) (he.trans_le hx)

end PaddedSolutionFamily

/-- The original packet data determine an actual family of smooth spatial
solutions and locally uniform barriers. Smoothness in the parameter is
proved separately from the implicit-family identification. -/
theorem nonempty_packetSolutionFamily {n : ℕ} {κIndex : Type*} [Fintype κIndex]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n+1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n+1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a)
    (κ cR cI : κIndex → ℝ) (v : κIndex → Fin (n+1) → ℝ)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n+1) j) 1)) = (l : ℝ)*(2*Real.pi)/100)
    (lam : ℝ) (hlam : 0 < lam) (zbase : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (hzbase : zbase ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a) :
    Nonempty (PaddedSolutionFamily (n+1) a
      (paddedLatticeBasis (m := n+2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R))
      (packetPaddedBackground n a ha lam) (packetPaddedSource R h a ha κ cR cI v lam)) := by
  classical
  obtain ⟨D,hD,hbar⟩ := exists_packet_family_with_locally_uniform_barriers
    R h a hh ha κ cR cI v hfreq lam hlam zbase hzbase
  let S : ∀ z, PeriodicQuaternionicSolution (D z) :=
    fun z => Classical.choice (D z).nonempty_solution
  refine ⟨⟨D,S,hD,?_⟩⟩
  intro z₀ hz₀
  obtain ⟨ρ,hρ,hρsub,C,c,hc,hcC,hbound⟩ := hbar z₀ hz₀
  exact ⟨ρ,hρ,hρsub,C,c,hc,hcC,fun z hz => hbound z hz (S z)⟩

end OAI.Analysis.Fourier.WavePackets
