import OAI.Analysis.PDE.Schauder.Calculus.PacketPushbackCore
import OAI.Analysis.Fourier.WavePackets.CalculusPacketPushbackGeometry

open Set Module
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Green OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Current

variable {n : ℕ} {ι : Type*} [Fintype ι]
  {R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)}
  {h a : ℝ} {ha : 0 < a} {κ cR cI : ι → ℝ} {v : ι → Fin (n + 1) → ℝ}
  {lam : ℝ} {z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3} {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 → ℝ}
  {α : ℝ} {U : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4
local notation "e" => paddedPhysicalSplit (n + 1)
local notation "b" => paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)
local notation "D" => OAI.Analysis.Normed.Function.Holder.C2Holder.LatticeDirichletSpace (hΩK := hΩK) (α := α) e b
local instance packetFieldDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance packetFieldDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance packetFieldSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance packetFieldSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem contDiffAt_packetPushback (hr : Continuous r)
    (hrd : ∀ x, r x < 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x < 0)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) (z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)
    (hz : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) (w : D) {y : E}
    (hy : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0) :
    ContDiffAt ℝ 2 (packetPushback a ha lam z₀ z w) y := by
  apply OAI.Analysis.PDE.Schauder.contDiffAt_physicalPushback_local hr
  · exact ((contDiff_packetPaddedBackground n a ha lam).comp
      (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by norm_num)
  · exact (contDiffAt_paddedPhysicalTransport_slice (n + 1) a _ _ ha hz hy.le).of_le (by norm_num)
  · exact paddedPhysicalTransport_into_domain (n + 1) a _ _ ha hz₀ hrd hy

/-- The transformed implicit Hessian is exactly the Hessian of the
potential pushed onto the target physical fiber. -/
theorem PacketParameterFields.hessianField_eq_packetPushback
    (C : PacketParameterFields R h a ha κ cR cI v lam z₀ r α U)
    (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b) (hα : 0 ≤ α) (hr : Continuous r)
    (hrd : ∀ x, r x < 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x < 0)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3}
    (hzU : z ∈ U) (hz : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) (w : D) {y : E}
    (hy : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0) :
    let x := paddedPhysicalTransport (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) (OAI.Analysis.PDE.Green.energyComplexTime z₀) y
    let hx := paddedPhysicalTransport_into_domain (n + 1) a _ _ ha hz₀ hrd hy
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (C.analytic.hessianField J hα (z,w)) ⟨x,hx.le⟩ =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (packetPushback a ha lam z₀ z w) y := by
  dsimp only
  let Ψ := paddedPhysicalTransport (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) (OAI.Analysis.PDE.Green.energyComplexTime z₀)
  have hx := paddedPhysicalTransport_into_domain (n + 1) a _ _ ha hz₀ hrd hy
  have hxy := paddedPhysicalTransport_inverse (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z)
    (OAI.Analysis.PDE.Green.energyComplexTime z₀) ha hz hz₀ hy.le
  apply C.analytic.hessianField_eq_local_pushback J hα hr z w
    (fun y => packetPaddedBackground n a ha lam (z,y)) Ψ (Ψ y) y hx
  · exact ((contDiff_packetPaddedBackground n a ha lam).comp
      (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by norm_num)
  · exact (contDiffAt_paddedPhysicalTransport_slice (n + 1) a _ _ ha hz hy.le).of_le (by norm_num)
  · rfl
  · rw [C.background_value z hzU]
    simp only [pullPhysicalCoefficient,Ψ,hxy,packetPaddedBackgroundHessian]
  · rw [C.jacobian_value z hzU]
    simp only [packetTransportJ,physicalTransportJ,Ψ,hxy]
  · rw [C.curvature_value z hzU]
    simp only [packetTransportK,physicalTransportK,Ψ,hxy]

theorem PacketParameterFields.packetPushback_equation
    (C : PacketParameterFields R h a ha κ cR cI v lam z₀ r α U)
    (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b) (hα : 0 ≤ α) (hr : Continuous r)
    (hrp : OAI.Analysis.PDE.Dirichlet.LatticePeriodic e b r)
    (hrd : ∀ x, r x < 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x < 0)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3}
    (hzU : z ∈ U) (hz : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) (w : D)
    (hzero : C.analytic.periodicOperator J hrp hα (z,w) = 0)
    {y : E} (hy : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0) :
    OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (packetPushback a ha lam z₀ z w) y) =
      packetPaddedSource R h a ha κ cR cI v lam (z,y) := by
  have hfield := C.hessianField_eq_packetPushback J hα hr hrd hz₀ hzU hz w hy
  have he := C.analytic.local_pushback_equation J hα hrp hzU w hzero _ _ _ y hfield
  rw [C.source_value z hzU] at he
  have hxy := paddedPhysicalTransport_inverse (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z)
    (OAI.Analysis.PDE.Green.energyComplexTime z₀) ha hz hz₀ hy.le
  simpa only [pullPhysicalCoefficient,hxy,packetPushback] using! he

theorem PacketParameterFields.packetPushback_positive
    (C : PacketParameterFields R h a ha κ cR cI v lam z₀ r α U)
    (J : OAI.Analysis.PDE.Schauder.LatticeJetLifts hΩK α e b) (hα : 0 ≤ α) (hr : Continuous r)
    (hrd : ∀ x, r x < 0 ↔ paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x < 0)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3}
    (hzU : z ∈ U) (hz : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) (w : D)
    (hpos : C.analytic.PositiveAt J hα (z,w))
    {y : E} (hy : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y < 0) :
    (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (packetPushback a ha lam z₀ z w) y)).PosDef := by
  exact C.analytic.local_pushback_positive J hα z w hpos _ _ _ y
    (contDiffAt_packetPushback hr hrd hz₀ z hz w hy)
    (C.hessianField_eq_packetPushback J hα hr hrd hz₀ hzU hz w hy)

end OAI.Analysis.Fourier.WavePackets
