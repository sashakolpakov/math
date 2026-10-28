import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.InverseJets

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Schauder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def parameterDerivative (f : ℝ × E → F) (p : ℝ × E) : F :=
  deriv (fun t => f (t,p.2)) p.1

theorem hasDerivAt_parameter_slice {f : ℝ × E → F} {t : ℝ} {x : E}
    (hf : DifferentiableAt ℝ f (t,x)) :
    HasDerivAt (fun s => f (s,x)) (fderiv ℝ f (t,x) (1,0)) t := by
  simpa only [Function.comp_def] using!
    hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))

theorem parameterDerivative_eq {f : ℝ × E → F} {p : ℝ × E}
    (hf : DifferentiableAt ℝ f p) :
    parameterDerivative f p = fderiv ℝ f p (1,0) :=
  (hasDerivAt_parameter_slice hf).deriv

theorem contDiffOn_parameterDerivative {f : ℝ × E → F} {U : Set ℝ}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f {p | p.1 ∈ U}) :
    ContDiffOn ℝ ∞ (parameterDerivative f) {p | p.1 ∈ U} := by
  have hopen : IsOpen {p : ℝ × E | p.1 ∈ U} := hU.preimage continuous_fst
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ f) {p | p.1 ∈ U} :=
    hf.fderiv_of_isOpen hopen (by simp)
  apply (hD.clm_apply contDiffOn_const).congr
  intro p hp
  exact parameterDerivative_eq ((hf p hp).contDiffAt (hopen.mem_nhds hp) |>.differentiableAt (by simp))

theorem contDiff_parameter_space_slice {f : ℝ × E → F} {U : Set ℝ}
    (hf : ContDiffOn ℝ ∞ f {p | p.1 ∈ U}) {t : ℝ} (ht : t ∈ U) :
    ContDiff ℝ ∞ (fun x => f (t,x)) := by
  rw [← contDiffOn_univ]
  exact hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => ht)

omit [NormedSpace ℝ E] in
theorem parameterDerivative_periodic {f : ℝ × E → F} {U : Set ℝ}
    (hU : IsOpen U) {t : ℝ} (ht : t ∈ U) (v : E)
    (hp : ∀ s ∈ U, ∀ x, f (s,x+v) = f (s,x)) (x : E) :
    parameterDerivative f (t,x+v) = parameterDerivative f (t,x) := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hU.mem_nhds ht] with s hs
  exact hp s hs x

end OAI.Analysis.PDE.Schauder
