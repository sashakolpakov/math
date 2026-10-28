import OAI.Analysis.Fourier.WavePackets.Packet.Coefficients

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open scoped Topology ContDiff

/-- The background Hessian and source in the pulled-back packet equation
admit actual smooth periodic coefficient extensions. -/
theorem exists_packet_data_extensions {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n + 1) j) 1)) = (l : ℝ) * (2 * Real.pi) / 100)
    (lam : ℝ) (z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖)
    {T : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)} (hT : IsCompact T) :
    ∃ (B : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 →
        OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 →L[ℝ] ℝ)
      (F : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3 × OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 → ℝ),
      ContDiff ℝ ∞ B ∧ ContDiff ℝ ∞ F ∧
      (∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit (n + 1))
        (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)) (fun x => B (z,x))) ∧
      (∀ z, OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit (n + 1))
        (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)) (fun x => F (z,x))) ∧
      ∀ z ∈ T, ∀ x, paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0 →
        B =ᶠ[𝓝 (z,x)] pullPhysicalCoefficient (n + 1) a z₀ (packetPaddedBackgroundHessian n a ha lam) ∧
        F =ᶠ[𝓝 (z,x)] pullPhysicalCoefficient (n + 1) a z₀ (packetPaddedSource R h a ha κ cR cI v lam) := by
  obtain ⟨B, hBs, hBp, hBe⟩ := exists_pullPhysicalCoefficient_extension (n + 1) a z₀ ha hz₀
    (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)) hT
    (packetPaddedBackgroundHessian n a ha lam) (contDiff_packetPaddedBackgroundHessian n a ha lam)
    (packetPaddedBackgroundHessian_periodic R a ha lam)
  obtain ⟨F, hFs, hFp, hFe⟩ := exists_pullPhysicalCoefficient_extension (n + 1) a z₀ ha hz₀
    (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)) hT
    (packetPaddedSource R h a ha κ cR cI v lam) (contDiff_packetPaddedSource R h a hh ha κ cR cI v lam)
    (packetPaddedSource_periodic R h a ha κ cR cI v hfreq lam)
  exact ⟨B,F,hBs,hFs,hBp,hFp,fun z hz x hx => ⟨hBe z hz x hx,hFe z hz x hx⟩⟩

end OAI.Analysis.Fourier.WavePackets
