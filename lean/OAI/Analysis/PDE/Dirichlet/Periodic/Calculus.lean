import OAI.Analysis.PDE.Dirichlet.Periodic.Representatives
import OAI.Analysis.PDE.Dirichlet.Translation

open Set Module
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion

variable {E P V ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]
  {e : E ≃L[ℝ] P × V} {b : Basis ι ℝ P}

omit [Fintype ι] in
theorem LatticePeriodic.comp {W X : Type*} {f : E → W} (hf : LatticePeriodic e b f)
    (g : W → X) : LatticePeriodic e b (fun x ↦ g (f x)) := by
  intro x l
  exact congrArg g (hf x l)

omit [Fintype ι] in
theorem LatticePeriodic.add {f g : E → ℝ} (hf : LatticePeriodic e b f)
    (hg : LatticePeriodic e b g) : LatticePeriodic e b (fun x ↦ f x + g x) := by
  intro x l
  exact congrArg₂ (· + ·) (hf x l) (hg x l)

omit [Fintype ι] in
theorem LatticePeriodic.smul {f : E → ℝ} (hf : LatticePeriodic e b f) (c : ℝ) :
    LatticePeriodic e b (fun x ↦ c • f x) := hf.comp (fun y ↦ c • y)

theorem lattice_translate_eq (e : E ≃L[ℝ] P × V) (x : E) (l : P) :
    e.symm ((e x).1 + l, (e x).2) = e.symm (l, 0) + x := by
  apply e.injective
  simp only [e.apply_symm_apply, map_add]
  exact Prod.ext (add_comm _ _) (zero_add _).symm

omit [Fintype ι] in
theorem LatticePeriodic.fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : LatticePeriodic e b f) : LatticePeriodic e b (_root_.fderiv ℝ f) := by
  intro x l
  let t : E := e.symm ((l : P), 0)
  have htranslate : (fun z ↦ f (t + z)) = f := by
    funext z
    rw [show t + z = e.symm ((e z).1 + (l : P), (e z).2) from
      (lattice_translate_eq e z (l : P)).symm]
    exact hf z l
  rw [lattice_translate_eq]
  change _root_.fderiv ℝ f (t + x) = _root_.fderiv ℝ f x
  calc
    _ = _root_.fderiv ℝ (fun z ↦ f (t + z)) x := (fderiv_comp_add_left t).symm
    _ = _ := by rw [htranslate]

omit [Fintype ι] in
theorem LatticePeriodic.quaternionHessian {n s : ℕ}
    {e : CoordinateSpace n s ≃L[ℝ] P × V} {b : Basis ι ℝ P}
    {f : CoordinateSpace n s → ℝ} (hf : LatticePeriodic e b f)
    (slots : Fin s → Quaternion ℝ) :
    LatticePeriodic e b (OAI.Analysis.PDE.Dirichlet.quaternionHessian slots f) := by
  intro x l
  unfold OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.PDE.Dirichlet.realHessian
  rw [hf.fderiv.fderiv x l]

end OAI.Analysis.PDE.Dirichlet
