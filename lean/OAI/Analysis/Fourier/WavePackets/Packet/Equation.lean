import OAI.Analysis.Fourier.WavePackets.Packet.Symbol
import OAI.Analysis.Fourier.WavePackets.Dirichlet.Closed

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Schauder
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder

variable {n : ℕ} {ι : Type*} [Fintype ι]
  {R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)}
  {h a : ℝ} {ha : 0 < a} {κ cR cI : ι → ℝ} {v : ι → Fin (n + 1) → ℝ}
  {lam : ℝ} {z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3} {C : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4
local notation "b" => paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)

theorem PacketSmoothCoefficients.referenceValue_positive
    (A : PacketSmoothCoefficients R h a ha κ cR cI v lam z₀ C)
    (S : PaddedSolutionFamily (n + 1) a b
      (packetPaddedBackground n a ha lam) (packetPaddedSource R h a ha κ cR cI v lam))
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3}
    (hzC : z ∈ C) (hz : z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a) {x : E}
    (hx : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0) :
    (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.mooreChartMatrix (A.background (z,x)) (A.jacobian (z,x)) (A.curvature (z,x))
      (fderiv ℝ (fun q => S.referenceValue z₀ (z,q)) x)
      (fderiv ℝ (fderiv ℝ (fun q => S.referenceValue z₀ (z,q))) x))).PosDef := by
  rw [A.referenceValue_matrix S hz₀ hzC hz hx]
  apply (S.solution z).closed_positive
  apply ((S.physical z hz).closed _).mpr
  exact (paddedPhysicalTransport_defining (n + 1) a _ _ ha hz.1.le hx).trans_le hx

theorem PacketSmoothCoefficients.referenceValue_equation
    (A : PacketSmoothCoefficients R h a ha κ cR cI v lam z₀ C)
    (S : PaddedSolutionFamily (n + 1) a b
      (packetPaddedBackground n a ha lam) (packetPaddedSource R h a ha κ cR cI v lam))
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3}
    (hzC : z ∈ C) (hz : z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a) {x : E}
    (hx : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0) :
    OAI.LinearAlgebra.Moore.mooreDet (n + 2)
      (OAI.Analysis.PDE.Dirichlet.mooreChartMatrix (A.background (z,x)) (A.jacobian (z,x)) (A.curvature (z,x))
        (fderiv ℝ (fun q => S.referenceValue z₀ (z,q)) x)
        (fderiv ℝ (fderiv ℝ (fun q => S.referenceValue z₀ (z,q))) x)) = A.source (z,x) := by
  rw [A.referenceValue_matrix S hz₀ hzC hz hx]
  have hy := (paddedPhysicalTransport_defining (n + 1) a _ _ ha hz.1.le hx).trans_le hx
  rw [(S.solution z).closed_equation _ (((S.physical z hz).closed _).mpr hy)]
  rw [(S.physical z hz).density,(A.exact_germs z hzC x hx).2.2.2.eq_of_nhds]
  rfl

end OAI.Analysis.Fourier.WavePackets
