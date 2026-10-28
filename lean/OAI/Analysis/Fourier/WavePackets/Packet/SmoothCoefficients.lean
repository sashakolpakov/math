import OAI.Analysis.Fourier.WavePackets.Packet.CoefficientExtensions
import OAI.Analysis.Fourier.WavePackets.TransportExtension

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module Filter OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped ContDiff Topology

structure PacketSmoothCoefficients {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (ha : 0 < a) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    (lam : ℝ) (z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (T : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)) where
  jacobian : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 →
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4
  curvature : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 →
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4
  background : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 →
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 →L[ℝ] ℝ
  source : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 → ℝ
  jacobian_smooth : ContDiff ℝ ∞ jacobian
  curvature_smooth : ContDiff ℝ ∞ curvature
  background_smooth : ContDiff ℝ ∞ background
  source_smooth : ContDiff ℝ ∞ source
  jacobian_periodic : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit (n + 1))
    (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)) (fun x => jacobian (z,x))
  curvature_periodic : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit (n + 1))
    (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)) (fun x => curvature (z,x))
  background_periodic : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit (n + 1))
    (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)) (fun x => background (z,x))
  source_periodic : ∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit (n + 1))
    (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)) (fun x => source (z,x))
  exact_germs : ∀ z ∈ T, ∀ x, paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0 →
    jacobian =ᶠ[𝓝 (z,x)] packetTransportJ (n + 1) a z₀ ∧
    curvature =ᶠ[𝓝 (z,x)] packetTransportK (n + 1) a z₀ ∧
    background =ᶠ[𝓝 (z,x)] pullPhysicalCoefficient (n + 1) a z₀ (packetPaddedBackgroundHessian n a ha lam) ∧
    source =ᶠ[𝓝 (z,x)] pullPhysicalCoefficient (n + 1) a z₀ (packetPaddedSource R h a ha κ cR cI v lam)

/-- Keep the actual smooth coefficient extensions, rather than forgetting
them after their first Hölder lift. This permits additional spatial flows. -/
theorem nonempty_packetSmoothCoefficients {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n + 1) j) 1)) = (l : ℝ) * (2 * Real.pi) / 100)
    (lam : ℝ) (z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖)
    {T : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)} (hT : IsCompact T)
    (hTreg : ∀ z ∈ T, a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) :
    Nonempty (PacketSmoothCoefficients R h a ha κ cR cI v lam z₀ T) := by
  obtain ⟨J,K,hJ,hK,hJp,hKp,heJK⟩ := exists_packetTransport_extensions (n + 1) a z₀ ha hz₀
    (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)) hT hTreg
  obtain ⟨B,F,hB,hF,hBp,hFp,heBF⟩ := exists_packet_data_extensions R h a hh ha κ cR cI v hfreq lam z₀ hz₀ hT
  refine ⟨⟨J,K,B,F,hJ,hK,hB,hF,hJp,hKp,hBp,hFp,?_⟩⟩
  intro z hz x hx
  exact ⟨(heJK z hz x hx).1,(heJK z hz x hx).2,(heBF z hz x hx).1,(heBF z hz x hx).2⟩

end OAI.Analysis.Fourier.WavePackets
