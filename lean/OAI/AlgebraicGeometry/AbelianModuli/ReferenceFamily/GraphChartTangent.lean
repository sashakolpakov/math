import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.KernelGraphCoordinates
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.LocalGraphChart

/-! # Graph Chart Tangent -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GraphChartTangent

noncomputable section

/-! The derivative of the actual inverse graph chart is a linear
isomorphism from its coordinates to the defining differential's kernel. -/

open Filter OAI.AlgebraicGeometry.ComplexPoints.Analytic.LocalGraphChart
open scoped _root_.Topology ContDiff

variable {U V W : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem graphChart_derivative_kernel (F : (U × V) → W)
    (e : OpenPartialHomeomorph {z | F z = 0} U)
    (z : {z | F z = 0}) (hz : z ∈ e.source)
    (hG : ContDiffOn ℂ ω (fun u => (e.symm u).val) e.target)
    (hF : DifferentiableAt ℂ F z.val) :
    ∀ u, fderiv ℂ F z.val (fderiv ℂ (fun u => (e.symm u).val) (e z) u) = 0 := by
  let G : U → U × V := fun u => (e.symm u).val
  have hg : DifferentiableAt ℂ G (e z) :=
    (hG.contDiffAt (e.open_target.mem_nhds (e.map_source hz))).differentiableAt (by simp)
  have hval : G (e z) = z.val := congrArg Subtype.val (e.left_inv hz)
  have hF' : HasFDerivAt F (fderiv ℂ F z.val) (G (e z)) := hval.symm ▸ hF.hasFDerivAt
  have hd := hF'.comp (e z) hg.hasFDerivAt
  have hd0 : HasFDerivAt (fun _ : U => (0 : W))
      ((fderiv ℂ F z.val).comp (fderiv ℂ G (e z))) (e z) := by
    apply hd.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun u => (e.symm u).property.symm)
  have heq := hd0.unique (hasFDerivAt_const (0 : W) (e z))
  intro u
  exact DFunLike.congr_fun heq u

omit [NormedSpace ℂ W] in
theorem graphChart_derivative_fst (F : (U × V) → W)
    (e : OpenPartialHomeomorph {z | F z = 0} U)
    (z : {z | F z = 0}) (hz : z ∈ e.source)
    (he : ∀ t, e t = t.val.1)
    (hG : ContDiffOn ℂ ω (fun u => (e.symm u).val) e.target) :
    ∀ u, (fderiv ℂ (fun u => (e.symm u).val) (e z) u).1 = u := by
  let G : U → U × V := fun u => (e.symm u).val
  have hg : DifferentiableAt ℂ G (e z) :=
    (hG.contDiffAt (e.open_target.mem_nhds (e.map_source hz))).differentiableAt (by simp)
  have hf : (fun u => (G u).1) =ᶠ[𝓝 (e z)] (fun u => u) := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hz)] with u hu
    exact (he (e.symm u)).symm.trans (e.right_inv hu)
  have hd0 := (ContinuousLinearMap.fst ℂ U V).hasFDerivAt.comp (e z) hg.hasFDerivAt
  have hd := hd0.congr_of_eventuallyEq hf.symm
  have heq := hd.unique (hasFDerivAt_id (e z))
  intro u
  exact DFunLike.congr_fun heq u

theorem graphChart_tangent_equiv (F : (U × V) → W)
    (e : OpenPartialHomeomorph {z | F z = 0} U)
    (z : {z | F z = 0}) (hz : z ∈ e.source)
    (he : ∀ t, e t = t.val.1)
    (hG : ContDiffOn ℂ ω (fun u => (e.symm u).val) e.target)
    (hF : DifferentiableAt ℂ F z.val)
    (hreg : ((fderiv ℂ F z.val).comp (ContinuousLinearMap.inr ℂ U V)).IsInvertible) :
    ∃ d : U ≃ₗ[ℂ] (fderiv ℂ F z.val).toLinearMap.ker,
      ∀ u, (d u).val = fderiv ℂ (fun u => (e.symm u).val) (e z) u := by
  obtain ⟨r, hr⟩ := hreg
  have hblock (v : V) : (fderiv ℂ F z.val).toLinearMap (0, v) = r v :=
    DFunLike.congr_fun hr.symm v
  let c := KernelGraphCoordinates.kernelFreeEquiv (fderiv ℂ F z.val).toLinearMap r.toLinearEquiv hblock
  refine ⟨c.symm, ?_⟩
  intro u
  have hw := graphChart_derivative_kernel F e z hz hG hF u
  have hf := graphChart_derivative_fst F e z hz he hG u
  exact congrArg Subtype.val
    (KernelGraphCoordinates.kernelFreeEquiv_inverse_characterization (fderiv ℂ F z.val).toLinearMap r.toLinearEquiv hblock
      u (fderiv ℂ (fun u => (e.symm u).val) (e z) u) hw hf)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.GraphChartTangent
