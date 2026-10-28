import OAI.Analysis.PDE.Concentration.CurrentDivergence

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion Matrix
open scoped Matrix ContDiff

local instance {n : ℕ} : NormedAddCommGroup (Matrix (Fin n) (Fin n) (Quaternion ℝ)) :=
  inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → Quaternion ℝ))
local instance {n : ℕ} : NormedSpace ℝ (Matrix (Fin n) (Fin n) (Quaternion ℝ)) :=
  inferInstanceAs (NormedSpace ℝ (Fin n → Fin n → Quaternion ℝ))
local instance {n : ℕ} : ContinuousSMul ℝ (Matrix (Fin n) (Fin n) (Quaternion ℝ)) :=
  inferInstanceAs (ContinuousSMul ℝ (Fin n → Fin n → Quaternion ℝ))
local instance {n : ℕ} : ContinuousConstSMul ℝ (Matrix (Fin n) (Fin n) (Quaternion ℝ)) :=
  inferInstanceAs (ContinuousConstSMul ℝ (Fin n → Fin n → Quaternion ℝ))

noncomputable def matrixConjugationCLM {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) →L[ℝ] Matrix (Fin n) (Fin n) (Quaternion ℝ) where
  toFun M := (OAI.Analysis.PDE.Dirichlet.realLift R)ᴴ * M * OAI.Analysis.PDE.Dirichlet.realLift R
  map_add' M N := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' r M := by simp []
  cont := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [Matrix.mul_apply]
    fun_prop

theorem matrixConjugationCLM_apply {n : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (M : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    matrixConjugationCLM R M = (OAI.Analysis.PDE.Dirichlet.realLift R)ᴴ * M * OAI.Analysis.PDE.Dirichlet.realLift R := rfl

theorem slot_action_coordinateVector {n s : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (p : Fin n × Fin s) :
    OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R) (OAI.Analysis.PDE.Dirichlet.coordinateVector p) =
      ∑ c, R c p.1 • OAI.Analysis.PDE.Dirichlet.coordinateVector (c, p.2) := by
  ext q
  change OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R) (OAI.Analysis.PDE.Dirichlet.coordinateVector p) q = _
  rw [realMatrixAction_coordinateVector]
  by_cases h : q.2 = p.2
  all_goals simp [slotLift, OAI.Analysis.PDE.Dirichlet.coordinateVector, Pi.single_apply, Prod.ext_iff, h]

noncomputable def rotatedCurrent {n s : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ) :=
  matrixConjugationCLM R ∘ A ∘ OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R)

theorem rotatedCurrent_apply {n s : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    (A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ)) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    rotatedCurrent R A x = (OAI.Analysis.PDE.Dirichlet.realLift R)ᴴ * A (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R) x) * OAI.Analysis.PDE.Dirichlet.realLift R :=
  matrixConjugationCLM_apply R _

theorem contDiffAt_rotatedCurrent {n s : ℕ} {N : ℕ∞ω} (R : Matrix (Fin n) (Fin n) ℝ)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ)} {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s}
    (hA : ContDiffAt ℝ N A (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R) x)) :
    ContDiffAt ℝ N (rotatedCurrent R A) x :=
  (matrixConjugationCLM R).contDiff.contDiffAt.comp x
    (hA.comp x (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R)).contDiff.contDiffAt)

theorem fderiv_rotatedCurrent_coordinate {n s : ℕ} (R : Matrix (Fin n) (Fin n) ℝ)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ)} {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s}
    (hA : DifferentiableAt ℝ A (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R) x)) (p : Fin n × Fin s) :
    fderiv ℝ (rotatedCurrent R A) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p) =
      rotatedCurrentDerivative R
        (fun q => fderiv ℝ A (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R) x) (OAI.Analysis.PDE.Dirichlet.coordinateVector q)) p := by
  have hd := (matrixConjugationCLM R).hasFDerivAt.comp x
    (hA.hasFDerivAt.comp x (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R)).hasFDerivAt)
  have hderiv : fderiv ℝ (rotatedCurrent R A) x =
      (matrixConjugationCLM R).comp
        ((fderiv ℝ A (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R) x)).comp (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R))) :=
    hd.fderiv
  rw [hderiv]
  simp only [ContinuousLinearMap.comp_apply, slot_action_coordinateVector, map_sum,
    map_smul, matrixConjugationCLM_apply, rotatedCurrentDerivative]

theorem rotatedCurrent_strongDivergence_zero {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {R : Matrix (Fin n) (Fin n) ℝ} (hR : R * Rᵀ = 1)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ)} {x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s}
    (hA : DifferentiableAt ℝ A (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R) x))
    (hdiv : ∀ b, OAI.Analysis.Calculus.Quaternion.strongDivergence e
      (fun p => fderiv ℝ A (OAI.Analysis.PDE.Dirichlet.realMatrixAction (slotLift R) x) (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) b = 0)
    (b : Fin n) :
    OAI.Analysis.Calculus.Quaternion.strongDivergence e (fun p => fderiv ℝ (rotatedCurrent R A) x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) b = 0 := by
  simp_rw [fderiv_rotatedCurrent_coordinate R hA]
  exact strongDivergence_rotatedCurrentDerivative_zero e hR _ hdiv b

end OAI.Analysis.PDE.Concentration
