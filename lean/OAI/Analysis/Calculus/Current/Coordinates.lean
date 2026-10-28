import OAI.Analysis.Calculus.Current.Strong
import OAI.Analysis.Calculus.Quaternion.CurrentOperations

/-! The current's separate real/imaginary derivatives as genuine joint derivatives. -/

noncomputable section
namespace OAI.Analysis.Calculus.Current

open scoped Matrix Matrix.Norms.Elementwise

abbrev CurrentSpace (d : ℕ) := (Index d → ℝ) × (Index d → ℂ)

def currentDirection {d : ℕ} (p : Index d × Fin 3) : CurrentSpace d :=
  ![(Pi.single p.1 1, 0), (0, Pi.single p.1 1), (0, Pi.single p.1 Complex.I)] p.2

theorem deriv_affineLine {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (v : E) :
    deriv (fun t : ℝ => f (x + t • v)) 0 = fderiv ℝ f x v := by
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hF : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by
    simpa only [zero_smul, add_zero] using hf.hasFDerivAt
  exact (hF.comp_hasDerivAt 0 hline).deriv

theorem fderiv_matrix_entry {E m : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype m] {A : E → Matrix m m (Quaternion ℝ)} {x : E}
    (hA : DifferentiableAt ℝ A x) (v : E) (a b : m) :
    fderiv ℝ (fun y => A y a b) x v = (fderiv ℝ A x v) a b := by
  have h₁ := (hasFDerivAt_pi'.mp hA.hasFDerivAt) a
  have h₂ := (hasFDerivAt_pi'.mp h₁) b
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using!
    congrArg (fun L => L v) h₂.fderiv

theorem differentiableAt_matrix_entry {E m : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype m] {A : E → Matrix m m (Quaternion ℝ)} {x : E}
    (hA : DifferentiableAt ℝ A x) (a b : m) :
    DifferentiableAt ℝ (fun y => A y a b) x :=
  ((hasFDerivAt_pi'.mp ((hasFDerivAt_pi'.mp hA.hasFDerivAt) a)) b).differentiableAt

theorem fderiv_currentDirection {d : ℕ}
    {A : (Index d → ℝ) → (Index d → ℂ) → Matrix (Index d) (Index d) (Quaternion ℝ)}
    {x : Index d → ℝ} {z : Index d → ℂ}
    (hA : DifferentiableAt ℝ (fun p : CurrentSpace d => A p.1 p.2) (x, z))
    (p : Index d × Fin 3) :
    fderiv ℝ (fun q : CurrentSpace d => A q.1 q.2) (x, z) (currentDirection p) =
      threeSlotMatrixDerivative A x z p := by
  apply Matrix.ext
  intro a b
  rw [← fderiv_matrix_entry hA]
  have he := differentiableAt_matrix_entry hA a b
  have hd := (deriv_affineLine he (currentDirection p)).symm
  obtain ⟨c, α⟩ := p
  fin_cases α
  all_goals
    convert hd using 1
    apply congrArg (fun f : ℝ → Quaternion ℝ => deriv f 0)
    funext t
    congr 1 ; ext i ;
      simp [currentDirection]

end OAI.Analysis.Calculus.Current
