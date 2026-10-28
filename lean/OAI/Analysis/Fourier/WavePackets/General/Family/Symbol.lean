import OAI.Analysis.Fourier.WavePackets.General.Family.Extensions
import OAI.Analysis.Fourier.WavePackets.General.Family.Solution
import OAI.Analysis.Fourier.WavePackets.Packet.Symbol
import OAI.Analysis.Fourier.WavePackets.Dirichlet.Closed

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Module Filter OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Schauder OAI.LinearAlgebra.Moore
open OAI.Analysis.PDE.Dirichlet.ParameterDeformation
open scoped Topology ContDiff Matrix.Norms.Elementwise ComplexOrder

variable {Z P V ι : Type*} {m : ℕ}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4 ≃L[ℝ] P × V} {b : Basis ι ℝ P}
  {D : Z → PeriodicQuaternionicData OAI.Analysis.Calculus.Quaternion.fourSlots e b} {z₀ : Z} {U C : Set Z}
  {G : LocalDirichletFamily D z₀ U}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace m 4

theorem LocalDirichletFamily.backward_forward_germ (G : LocalDirichletFamily D z₀ U)
    {z : Z} (hz : z ∈ U) {x : E} (hx : (D z₀).defining x ≤ 0) :
    (fun y => G.backward (z,G.forward (z,y))) =ᶠ[𝓝 x] id := by
  have hp : (z,x) ∈ G.sourceNeighborhood := G.source_closed ⟨hz,hx⟩
  have hn := (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
    (G.source_open.mem_nhds hp)
  filter_upwards [hn] with y hy
  exact G.backward_forward (z,y) hy

theorem LocalDirichletFamily.forward_backward_germ (G : LocalDirichletFamily D z₀ U)
    {z : Z} (hz : z ∈ U) {y : E} (hy : (D z).defining y ≤ 0) :
    (fun x => G.forward (z,G.backward (z,x))) =ᶠ[𝓝 y] id := by
  have hp : (z,y) ∈ G.targetNeighborhood := G.target_closed ⟨hz,hy⟩
  have hn := (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
    (G.target_open.mem_nhds hp)
  filter_upwards [hn] with x hx
  exact G.forward_backward (z,x) hx

theorem SmoothFamilyCoefficients.jacobian_surjective (A : SmoothFamilyCoefficients G C)
    {z : Z} (hz : z ∈ U) (hzC : z ∈ C) {x : E} (hx : (D z₀).defining x ≤ 0) :
    Function.Surjective (A.jacobian (z,x)) := by
  rw [(A.exact_germs z hzC x hx).1.eq_of_nhds]
  exact OAI.Analysis.PDE.Dirichlet.ParameterDeformation.localFamilyJacobian_surjective G.source_open G.target_open
    G.forward_smooth G.backward_smooth (fun p hp => G.forward_mem p hp)
    (G.source_closed ⟨hz,hx⟩) (G.backward_forward_germ hz hx)

theorem SmoothFamilyCoefficients.referenceValue_matrix (A : SmoothFamilyCoefficients G C)
    (S : DirichletSolutionFamily D) {z : Z} (hz : z ∈ U) (hzC : z ∈ C)
    {x : E} (hx : (D z₀).defining x ≤ 0) :
    OAI.Analysis.PDE.Dirichlet.mooreChartMatrix (A.background (z,x)) (A.jacobian (z,x)) (A.curvature (z,x))
      (fderiv ℝ (fun q => G.referenceValue S (z,q)) x)
      (fderiv ℝ (fderiv ℝ (fun q => G.referenceValue S (z,q))) x) =
      OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun q => (D z).background q + (S z).u q)
        (G.forward (z,x)) := by
  let y := G.forward (z,x)
  let Ψ := fun q => G.backward (z,q)
  let f := fun q => G.referenceValue S (z,q)
  have hy : (D z).defining y ≤ 0 := G.forward_closed z hz x hx
  have hxy : Ψ y = x := G.backward_forward (z,x) (G.source_closed ⟨hz,hx⟩)
  have hB : ContDiffAt ℝ 2 (D z).background y :=
    (D z).background_smooth.contDiffAt.of_le (by simp)
  have hf : ContDiffAt ℝ 2 f x := (G.referenceValue_slice_contDiffAt S hz hx).of_le (by simp)
  have hΨ : ContDiffAt ℝ 2 Ψ y := (G.backward_slice_contDiffAt hz hy).of_le (by simp)
  have he := A.exact_germs z hzC x hx
  rw [he.1.eq_of_nhds,he.2.1.eq_of_nhds,he.2.2.1.eq_of_nhds]
  change OAI.Analysis.PDE.Dirichlet.mooreChartMatrix (fderiv ℝ (fderiv ℝ (D z).background) y) (fderiv ℝ Ψ y)
    (fderiv ℝ (fderiv ℝ Ψ) y) (fderiv ℝ f x) (fderiv ℝ (fderiv ℝ f) x) = _
  rw [mooreChartMatrix_eq_local_composition (D z).background f Ψ x y hxy hB hf hΨ]
  have hgerm : (fun q => (D z).background q + f (Ψ q)) =ᶠ[𝓝 y]
      (fun q => (D z).background q + (S z).u q) := by
    filter_upwards [G.forward_backward_germ hz hy] with q hq
    dsimp only [f,Ψ,OAI.Analysis.Fourier.WavePackets.LocalDirichletFamily.referenceValue]
    rw [hq]
    rfl
  unfold OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.PDE.Dirichlet.realHessian
  rw [(hgerm.fderiv (𝕜 := ℝ)).fderiv_eq]

theorem SmoothFamilyCoefficients.referenceValue_positive (A : SmoothFamilyCoefficients G C)
    (S : DirichletSolutionFamily D) {z : Z} (hz : z ∈ U) (hzC : z ∈ C)
    {x : E} (hx : (D z₀).defining x ≤ 0) :
    (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.mooreChartMatrix (A.background (z,x)) (A.jacobian (z,x)) (A.curvature (z,x))
      (fderiv ℝ (fun q => G.referenceValue S (z,q)) x)
      (fderiv ℝ (fderiv ℝ (fun q => G.referenceValue S (z,q))) x))).PosDef := by
  rw [A.referenceValue_matrix S hz hzC hx]
  exact (S z).closed_positive _ (G.forward_closed z hz x hx)

theorem SmoothFamilyCoefficients.referenceValue_equation (A : SmoothFamilyCoefficients G C)
    (S : DirichletSolutionFamily D) {z : Z} (hz : z ∈ U) (hzC : z ∈ C)
    {x : E} (hx : (D z₀).defining x ≤ 0) :
    OAI.LinearAlgebra.Moore.mooreDet m (OAI.Analysis.PDE.Dirichlet.mooreChartMatrix (A.background (z,x)) (A.jacobian (z,x)) (A.curvature (z,x))
      (fderiv ℝ (fun q => G.referenceValue S (z,q)) x)
      (fderiv ℝ (fderiv ℝ (fun q => G.referenceValue S (z,q))) x)) = A.source (z,x) := by
  rw [A.referenceValue_matrix S hz hzC hx,
    (S z).closed_equation _ (G.forward_closed z hz x hx),
    (A.exact_germs z hzC x hx).2.2.2.eq_of_nhds]
  rfl

end OAI.Analysis.Fourier.WavePackets
