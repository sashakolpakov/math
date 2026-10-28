import OAI.Analysis.PDE.Schauder.Calculus.Parameter.Derivative

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Schauder

variable {Z E F : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def parameterFDerivative (f : Z × E → F) (p : Z × E) : Z →L[ℝ] F :=
  fderiv ℝ (fun t => f (t,p.2)) p.1

theorem hasFDerivAt_parameter_slice {f : Z × E → F} {t : Z} {x : E}
    (hf : DifferentiableAt ℝ f (t,x)) :
    HasFDerivAt (fun s => f (s,x))
      ((fderiv ℝ f (t,x)).comp (ContinuousLinearMap.inl ℝ Z E)) t := by
  have hi : HasFDerivAt (fun s : Z => (s,x)) (ContinuousLinearMap.inl ℝ Z E) t := by
    change HasFDerivAt (fun s : Z => (s,x))
      ((ContinuousLinearMap.id ℝ Z).prod (0 : Z →L[ℝ] E)) t
    simpa only [id_eq] using (hasFDerivAt_id t).prodMk (hasFDerivAt_const x t)
  exact hf.hasFDerivAt.comp t hi

theorem parameterFDerivative_eq {f : Z × E → F} {p : Z × E}
    (hf : DifferentiableAt ℝ f p) :
    parameterFDerivative f p =
      (fderiv ℝ f p).comp (ContinuousLinearMap.inl ℝ Z E) :=
  (hasFDerivAt_parameter_slice hf).fderiv

theorem fderiv_space_slice {f : Z × E → F} {p : Z × E}
    (hf : DifferentiableAt ℝ f p) :
    fderiv ℝ (fun x => f (p.1,x)) p.2 =
      (fderiv ℝ f p).comp (ContinuousLinearMap.inr ℝ Z E) := by
  have hi : HasFDerivAt (fun x : E => (p.1,x)) (ContinuousLinearMap.inr ℝ Z E) p.2 := by
    change HasFDerivAt (fun x : E => (p.1,x))
      ((0 : E →L[ℝ] Z).prod (ContinuousLinearMap.id ℝ E)) p.2
    simpa only [id_eq] using (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  exact (hf.hasFDerivAt.comp p.2 hi).fderiv

theorem contDiffOn_parameterFDerivative {f : Z × E → F} {U : Set Z}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f {p | p.1 ∈ U}) :
    ContDiffOn ℝ ∞ (parameterFDerivative f) {p | p.1 ∈ U} := by
  have hopen : IsOpen {p : Z × E | p.1 ∈ U} := hU.preimage continuous_fst
  have hd := hf.fderiv_of_isOpen hopen (m := ∞) (by simp)
  apply (hd.clm_comp contDiffOn_const).congr
  intro p hp
  exact parameterFDerivative_eq ((hf p hp).contDiffAt (hopen.mem_nhds hp) |>.differentiableAt (by simp))

theorem contDiffOn_space_fderiv {f : Z × E → F} {U : Set Z}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f {p | p.1 ∈ U}) :
    ContDiffOn ℝ ∞ (fun p : Z × E => fderiv ℝ (fun x => f (p.1,x)) p.2)
      {p | p.1 ∈ U} := by
  have hopen : IsOpen {p : Z × E | p.1 ∈ U} := hU.preimage continuous_fst
  have hd := hf.fderiv_of_isOpen hopen (m := ∞) (by simp)
  apply (hd.clm_comp contDiffOn_const).congr
  intro p hp
  exact fderiv_space_slice ((hf p hp).contDiffAt (hopen.mem_nhds hp) |>.differentiableAt (by simp))

theorem contDiff_fixed_parameter_slice {f : Z × E → F} {U : Set Z}
    (hf : ContDiffOn ℝ ∞ f {p | p.1 ∈ U}) {t : Z} (ht : t ∈ U) :
    ContDiff ℝ ∞ (fun x => f (t,x)) := by
  rw [← contDiffOn_univ]
  exact hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => ht)

end OAI.Analysis.PDE.Schauder
