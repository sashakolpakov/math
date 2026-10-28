import OAI.Analysis.Fourier.WavePackets.TransportInverseGerm
import OAI.Analysis.Fourier.WavePackets.Packet.SmoothCoefficients
import OAI.Analysis.Fourier.WavePackets.Rough.Packet.Family
import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.MooreResidual

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter Module OAI.Analysis.Calculus.Current OAI.Analysis.PDE.Concentration OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.Analysis.PDE.Schauder
open scoped Topology ContDiff Matrix.Norms.Elementwise

theorem mooreChartMatrix_eq_local_composition {m : ℕ}
    (B f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 → ℝ) (Ψ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 → OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4)
    (x y : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4) (hxy : Ψ y = x)
    (hB : ContDiffAt ℝ 2 B y) (hf : ContDiffAt ℝ 2 f x) (hΨ : ContDiffAt ℝ 2 Ψ y) :
    OAI.Analysis.PDE.Dirichlet.mooreChartMatrix (fderiv ℝ (fderiv ℝ B) y) (fderiv ℝ Ψ y)
      (fderiv ℝ (fderiv ℝ Ψ) y) (fderiv ℝ f x) (fderiv ℝ (fderiv ℝ f) x) =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun q => B q + f (Ψ q)) y := by
  have hf' : ContDiffAt ℝ 2 f (Ψ y) := by simpa only [hxy] using hf
  unfold OAI.Analysis.PDE.Dirichlet.mooreChartMatrix OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.PDE.Dirichlet.realHessian
  congr 1
  funext i j
  have hadd : fderiv ℝ (fderiv ℝ (fun q => B q + f (Ψ q))) y =
      fderiv ℝ (fderiv ℝ B) y + fderiv ℝ (fderiv ℝ (fun q => f (Ψ q))) y := by
    simpa only [Function.comp_def] using! OAI.Analysis.PDE.Schauder.second_fderiv_add_at hB (hf'.comp y hΨ)
  rw [hadd]
  simp only [add_apply]
  congr 1
  simpa only [hxy] using (OAI.Analysis.PDE.Elliptic.second_fderiv_comp hf' hΨ
    (OAI.Analysis.PDE.Dirichlet.coordinateVector i) (OAI.Analysis.PDE.Dirichlet.coordinateVector j)).symm

variable {n : ℕ} {ι : Type*} [Fintype ι]
  {R : OAI.Analysis.Calculus.Current.SpatialSpace (n + 1) ≃L[ℝ] OAI.Analysis.Calculus.Current.SpatialSpace (n + 1)}
  {h a : ℝ} {ha : 0 < a} {κ cR cI : ι → ℝ} {v : ι → Fin (n + 1) → ℝ}
  {lam : ℝ} {z₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3} {C : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3)}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) 4
local notation "b" => paddedLatticeBasis (m := n + 2) (OAI.Analysis.PDE.Concentration.packetSpatialBasis R)

theorem PacketSmoothCoefficients.jacobian_surjective
    (A : PacketSmoothCoefficients R h a ha κ cR cI v lam z₀ C)
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3}
    (hzC : z ∈ C) (hz : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z‖) {x : E}
    (hx : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0) :
    Function.Surjective (A.jacobian (z,x)) := by
  rw [(A.exact_germs z hzC x hx).1.eq_of_nhds]
  exact physicalTransportJ_surjective (n + 1) a _ _ ha hz₀ hz hx

/-- The raw transformed symbol is the actual quaternionic Hessian of the
chosen target solution, including points on the spatial boundary. -/
theorem PacketSmoothCoefficients.referenceValue_matrix
    (A : PacketSmoothCoefficients R h a ha κ cR cI v lam z₀ C)
    (S : PaddedSolutionFamily (n + 1) a b
      (packetPaddedBackground n a ha lam) (packetPaddedSource R h a ha κ cR cI v lam))
    (hz₀ : a ≤ ‖OAI.Analysis.PDE.Green.energyComplexTime z₀‖) {z : OAI.Analysis.PDE.Dirichlet.CoordinateSpace 1 3}
    (hzC : z ∈ C) (hz : z ∈ OAI.Analysis.PDE.Concentration.physicalEnergyAnnulus a) {x : E}
    (hx : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) x ≤ 0) :
    OAI.Analysis.PDE.Dirichlet.mooreChartMatrix (A.background (z,x)) (A.jacobian (z,x)) (A.curvature (z,x))
      (fderiv ℝ (fun q => S.referenceValue z₀ (z,q)) x)
      (fderiv ℝ (fderiv ℝ (fun q => S.referenceValue z₀ (z,q))) x) =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun q => (S.data z).background q + (S.solution z).u q)
        (paddedPhysicalTransport (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime z) x) := by
  let y := paddedPhysicalTransport (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z₀) (OAI.Analysis.PDE.Green.energyComplexTime z) x
  let Ψ := paddedPhysicalTransport (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) (OAI.Analysis.PDE.Green.energyComplexTime z₀)
  let B := fun q => packetPaddedBackground n a ha lam (z,q)
  let f := fun q => S.referenceValue z₀ (z,q)
  have hy : paddedPhysicalDefining (n + 1) a (OAI.Analysis.PDE.Green.energyComplexTime z) y ≤ 0 :=
    (paddedPhysicalTransport_defining (n + 1) a _ _ ha hz.1.le hx).trans_le hx
  have hxy : Ψ y = x := paddedPhysicalTransport_inverse (n + 1) a _ _ ha hz₀ hz.1.le hx
  have hB : ContDiffAt ℝ 2 B y := ((contDiff_packetPaddedBackground n a ha lam).comp
    (contDiff_const.prodMk contDiff_id)).contDiffAt.of_le (by norm_num)
  have hf : ContDiffAt ℝ 2 f x := (S.referenceValue_slice_smooth ha hz₀ z hx).of_le (by norm_num)
  have hΨ : ContDiffAt ℝ 2 Ψ y :=
    (contDiffAt_paddedPhysicalTransport_slice (n + 1) a _ _ ha hz.1.le hy).of_le (by norm_num)
  have he := A.exact_germs z hzC x hx
  rw [he.1.eq_of_nhds,he.2.1.eq_of_nhds,he.2.2.1.eq_of_nhds]
  change OAI.Analysis.PDE.Dirichlet.mooreChartMatrix (fderiv ℝ (fderiv ℝ B) y) (fderiv ℝ Ψ y)
    (fderiv ℝ (fderiv ℝ Ψ) y) (fderiv ℝ f x) (fderiv ℝ (fderiv ℝ f) x) = _
  rw [mooreChartMatrix_eq_local_composition B f Ψ x y hxy hB hf hΨ]
  have hgerm : (fun q => B q + f (Ψ q)) =ᶠ[𝓝 y]
      (fun q => (S.data z).background q + (S.solution z).u q) := by
    filter_upwards [paddedPhysicalTransport_inverse_germ (n + 1) a
      (OAI.Analysis.PDE.Green.energyComplexTime z) (OAI.Analysis.PDE.Green.energyComplexTime z₀) ha hz.1.le hz₀ hy] with q hq
    dsimp only [B,f,Ψ,OAI.Analysis.Fourier.WavePackets.PaddedSolutionFamily.referenceValue]
    rw [hq,(S.physical z hz).background]
    rfl
  unfold OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.PDE.Dirichlet.realHessian
  rw [(hgerm.fderiv (𝕜 := ℝ)).fderiv_eq]

end OAI.Analysis.Fourier.WavePackets
