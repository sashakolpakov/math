import OAI.Analysis.Fourier.WavePackets.Packet.FlowFields
import OAI.Analysis.Fourier.WavePackets.Packet.FlowGeometry

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open OAI.Analysis.PDE.Dirichlet.ParameterDeformation OAI.Analysis.PDE.Green OAI.Analysis.PDE.Schauder OAI.Analysis.Normed.Function.Holder
open scoped ContDiff Matrix.Norms.Elementwise

variable {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [CompleteSpace T]
  {n : ℕ} {ι : Type*} [Fintype ι]
  {R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)}
  {h a : ℝ} {ha : 0 < a} {κ cR cI : ι → ℝ} {v : ι → Fin (n + 1) → ℝ}
  {lam : ℝ} {z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3} {r : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4 → ℝ}
  {α : ℝ} {U C : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4
local notation "e" => paddedPhysicalSplit (n + 1)
local notation "b" => paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)

omit [CompleteSpace T] in
theorem PacketFlowFields.inverse_coefficient_values
    {A : PacketSmoothCoefficients R h a ha κ cR cI v lam z₀ C}
    {D : OAI.Analysis.PDE.Dirichlet.ParameterDeformation.PeriodicDomainDeformation (Z := T) e b r} (F : PacketFlowFields A D U α)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3}
    (hz : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) (hzC : z ∈ C) {t : T}
    (hp : (z,t) ∈ U ×ˢ {t : T | ‖t‖ < D.radius})
    (x : {x | r x ≤ 0}) (y : E)
    (hmap : D.map (t,x) = paddedPhysicalTransport (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) (OAI.Analysis.PDE.Green.energyComplexTime z₀) y)
    (hy : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (F.analytic.jacobian (z,t)) x = fderiv ℝ (packetFlowInverse D a z₀ z t) y ∧
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (F.analytic.curvature (z,t)) x = fderiv ℝ (fderiv ℝ (packetFlowInverse D a z₀ z t)) y ∧
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (F.analytic.background (z,t)) x =
      fderiv ℝ (fderiv ℝ (fun y => packetPaddedBackground n a ha lam (z,y))) y ∧
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (F.analytic.source (z,t)) x = packetPaddedSource R h a ha κ cR cI v lam (z,y) := by
  let Ψ := paddedPhysicalTransport (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) (OAI.Analysis.PDE.Green.energyComplexTime z₀)
  have hbase : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) (D.map (t,x)) ≤ 0 := by
    rw [hmap,paddedPhysicalTransport_defining (n + 1) a _ _ ha hz₀ hy]
    exact hy
  have hback : paddedPhysicalTransport (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime z)
      (D.map (t,x)) = y := by
    rw [hmap]
    exact paddedPhysicalTransport_inverse (n + 1) a _ _ ha hz hz₀ hy
  have he := A.exact_germs z hzC (D.map (t,x)) hbase
  have hj : A.jacobian (z,D.map (t,x)) = fderiv ℝ Ψ y := by
    rw [he.1.eq_of_nhds]
    simp only [packetTransportJ,physicalTransportJ,hback]
    rfl
  have hk : A.curvature (z,D.map (t,x)) = fderiv ℝ (fderiv ℝ Ψ) y := by
    rw [he.2.1.eq_of_nhds]
    simp only [packetTransportK,physicalTransportK,hback]
    rfl
  have hi : ContDiffAt ℝ 2 (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.inverseFamily D.map t) (D.map (t,x)) :=
    (OAI.Analysis.PDE.Dirichlet.ParameterDeformation.contDiff_inverseFamily_slice (U := {s : T | ‖s‖ < D.radius})
      (Φ := D.map) D.inverse_smooth hp.2).contDiffAt.of_le (by norm_num)
  have hΨ : ContDiffAt ℝ 2 Ψ y :=
    (contDiffAt_paddedPhysicalTransport_slice (n + 1) a _ _ ha hz hy).of_le (by norm_num)
  refine ⟨?_,?_,?_,?_⟩
  · rw [F.jacobian_value _ hp]
    exact flowJacobian_eq_fderiv D.map Ψ A.jacobian z t x y hmap.symm hi hΨ hj
  · rw [F.curvature_value _ hp]
    exact flowCurvature_eq_second_fderiv D.map Ψ A.jacobian A.curvature z t x y hmap.symm hi hΨ hj hk
  · rw [F.background_value _ hp]
    change A.background (z,D.map (t,x)) = _
    rw [he.2.2.1.eq_of_nhds]
    simp only [pullPhysicalCoefficient,hback,packetPaddedBackgroundHessian]
  · rw [F.source_value _ hp]
    change A.source (z,D.map (t,x)) = _
    rw [he.2.2.2.eq_of_nhds]
    simp only [pullPhysicalCoefficient,hback]

end OAI.Analysis.Fourier.WavePackets
