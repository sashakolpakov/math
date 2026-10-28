import OAI.Analysis.Fourier.WavePackets.Packet.BaseData

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green
open OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder
open scoped ContDiff

/-- The actual packet coefficients, with their physical values retained. -/
structure PacketParameterFields {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (ha : 0 < a) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    (lam : ℝ) (z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 → ℝ)
    (α : ℝ) (U : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)) where
  analytic : OAI.Analysis.PDE.Schauder.ParameterJetFields r α U (paddedPhysicalSplit (n + 1))
    (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R))
  jacobian_value : ∀ z ∈ U, ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (analytic.jacobian z) x =
    packetTransportJ (n + 1) a z₀ (z,x)
  curvature_value : ∀ z ∈ U, ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (analytic.curvature z) x =
    packetTransportK (n + 1) a z₀ (z,x)
  background_value : ∀ z ∈ U, ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (analytic.background z) x =
    pullPhysicalCoefficient (n + 1) a z₀ (packetPaddedBackgroundHessian n a ha lam) (z,x)
  source_value : ∀ z ∈ U, ∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value (analytic.source z) x =
    pullPhysicalCoefficient (n + 1) a z₀ (packetPaddedSource R h a ha κ cR cI v lam) (z,x)

theorem nonempty_packetParameterFields {n : ℕ} {ι : Type*} [Fintype ι]
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n + 1) j) 1)) = (l : ℝ) * (2 * Real.pi) / 100)
    (lam : ℝ) (z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖)
    {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 → ℝ} (hr : Continuous r)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit (n + 1))
      (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)) r)
    (hrl : ∀ x, r x ≤ 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {U T : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)} (hU : IsOpen U) (hT : IsCompact T) (hUT : U ⊆ T)
    (hTreg : ∀ z ∈ T, a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) :
    Nonempty (PacketParameterFields R h a ha κ cR cI v lam z₀ r α U) := by
  obtain ⟨C,hJ,hK,hB,hF⟩ := exists_packet_parameterJetFields R h a hh ha κ cR cI v hfreq
    lam z₀ hz₀ hr hrp hrl hα hα1 hU hT hUT hTreg
  exact ⟨⟨C,hJ,hK,hB,hF⟩⟩

variable {n : ℕ} {ι : Type*} [Fintype ι]
  {R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)}
  {h a : ℝ} {ha : 0 < a} {κ cR cI : ι → ℝ} {v : ι → Fin (n + 1) → ℝ}
  {lam : ℝ} {z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3} {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 → ℝ}
  {α : ℝ} {U : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)}

theorem PacketParameterFields.jacobian_base
    (C : PacketParameterFields R h a ha κ cR cI v lam z₀ r α U)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) (h0 : z₀ ∈ U)
    (hrl : ∀ x, r x ≤ 0 → paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0) :
    C.analytic.jacobian z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant (ContinuousLinearMap.id ℝ _) := by
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
  apply BoundedContinuousFunction.ext
  intro x
  rw [C.jacobian_value z₀ h0,OAI.Analysis.Normed.Function.Holder.HolderMap.value_constant]
  exact packetTransportJ_base (n + 1) a z₀ ha hz₀ (hrl x x.property)

theorem PacketParameterFields.curvature_base
    (C : PacketParameterFields R h a ha κ cR cI v lam z₀ r α U)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) (h0 : z₀ ∈ U)
    (hrl : ∀ x, r x ≤ 0 → paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0) :
    C.analytic.curvature z₀ = OAI.Analysis.Normed.Function.Holder.HolderMap.constant 0 := by
  apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
  apply BoundedContinuousFunction.ext
  intro x
  rw [C.curvature_value z₀ h0,OAI.Analysis.Normed.Function.Holder.HolderMap.value_constant]
  exact packetTransportK_base (n + 1) a z₀ ha hz₀ (hrl x x.property)

theorem PacketParameterFields.background_base_value
    (C : PacketParameterFields R h a ha κ cR cI v lam z₀ r α U)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) (h0 : z₀ ∈ U)
    (hrl : ∀ x, r x ≤ 0 → paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0)
    (x : {x | r x ≤ 0}) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.analytic.background z₀) x =
      fderiv ℝ (fderiv ℝ (fun y => packetPaddedBackground n a ha lam (z₀,y))) x := by
  rw [C.background_value z₀ h0,pullPhysicalCoefficient_base (n + 1) a z₀ ha hz₀ _ (hrl x x.property)]
  rfl

theorem PacketParameterFields.source_base_value
    (C : PacketParameterFields R h a ha κ cR cI v lam z₀ r α U)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) (h0 : z₀ ∈ U)
    (hrl : ∀ x, r x ≤ 0 → paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0)
    (x : {x | r x ≤ 0}) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.analytic.source z₀) x = packetPaddedSource R h a ha κ cR cI v lam (z₀,x) := by
  rw [C.source_value z₀ h0,pullPhysicalCoefficient_base (n + 1) a z₀ ha hz₀ _ (hrl x x.property)]

/-- Around every point of the open physical annulus, all coefficient
fields exist on a genuine parameter neighborhood. Its closed enlargement
stays away from the degenerating inner boundary. -/
theorem exists_packetParameterFields_near
    (R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1))
    (h a : ℝ) (hh : 0 < h) (ha : 0 < a) (κ cR cI : ι → ℝ) (v : ι → Fin (n + 1) → ℝ)
    (hfreq : ∀ i j, ∃ l : ℤ, inner ℝ (OAI.Analysis.PDE.Concentration.packetSpatialFrequency (κ i) (v i))
      (R (EuclideanSpace.single (finSuccEquiv (n + 1) j) 1)) = (l : ℝ) * (2 * Real.pi) / 100)
    (lam : ℝ) (z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3) (hz₀ : z₀ ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a)
    {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 → ℝ} (hr : Continuous r)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic (paddedPhysicalSplit (n + 1))
      (paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)) r)
    (hrl : ∀ x, r x ≤ 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall z₀ ρ ⊆ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a ∧
      Nonempty (PacketParameterFields R h a ha κ cR cI v lam z₀ r α (Metric.ball z₀ ρ)) := by
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp ((OAI.Analysis.PDE.Concentration.isOpen_physicalEnergyAnnulus a).mem_nhds hz₀)
  have hρ : 0 < δ / 2 := half_pos hδ
  have hclosed : Metric.closedBall z₀ (δ / 2) ⊆ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a :=
    (Metric.closedBall_subset_ball (by linarith)).trans hsub
  refine ⟨δ / 2,hρ,hclosed,?_⟩
  exact nonempty_packetParameterFields R h a hh ha κ cR cI v hfreq lam z₀ hz₀.1.le
    hr hrp hrl hα hα1 Metric.isOpen_ball (isCompact_closedBall z₀ (δ / 2))
    Metric.ball_subset_closedBall (fun z hz => (hclosed hz).1.le)

end OAI.Analysis.Fourier.WavePackets
