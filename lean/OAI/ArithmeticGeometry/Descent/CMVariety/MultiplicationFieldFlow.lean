import OAI.ArithmeticGeometry.Descent.CMVariety.ParametricFlow
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # Multiplication Field Flow -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.MultiplicationFieldFlow.Abelian

noncomputable section

/-!
Construct the derivative field of a local multiplication and prove that
its flows depend continuously on the base parameter, tangent vector, and
time. Smoothness of the field is derived from the multiplication map;
no separately smooth vector-field data are required.
-/

open Set _root_.Metric
open scoped NNReal

variable {P V : Type}
  [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Differentiate multiplication in its last variable at zero, then apply
that derivative to the fixed tangent-vector parameter. -/
def multiplicationField (m : P × (V × V) → V) : (P × V) × V → V :=
  fun q => fderiv ℝ (fun y => m (q.1.1, (q.2, y))) 0 q.1.2

omit [CompleteSpace P] [CompleteSpace V] in
theorem multiplicationField_contDiffAt
    (m : P × (V × V) → V) (p₀ : P)
    (hm : ContDiffAt ℝ 2 m (p₀, (0, 0))) :
    ContDiffAt ℝ 1 (multiplicationField m) ((p₀, 0), 0) := by
  let f : ((P × V) × V) → V → V := fun q y => m (q.1.1, (q.2, y))
  have hcoord : ContDiffAt ℝ 2
      (fun z : (((P × V) × V) × V) => (z.1.1.1, (z.1.2, z.2))) (((p₀, 0), 0), 0) := by
    fun_prop
  have hf : ContDiffAt ℝ 2 (Function.uncurry f) (((p₀, 0), 0), 0) :=
    hm.comp (((p₀, 0), 0), 0) hcoord
  have hd : ContDiffAt ℝ 1 (fun q => fderiv ℝ (f q) 0) ((p₀, 0), 0) :=
    hf.fderiv (g := fun _ => 0) contDiffAt_const (by norm_num)
  exact hd.clm_apply contDiffAt_fst.snd

/-- The multiplication-derived ODE has an actual continuously varying
local solution starting at the zero section. The base parameter and
tangent vector remain fixed throughout each solution. -/
theorem exists_continuous_multiplicationField_flow
    (m : P × (V × V) → V) (p₀ : P)
    (hm : ContDiffAt ℝ 2 m (p₀, (0, 0))) :
    ∃ (r : ℝ≥0), 0 < r ∧ ∃ ε : ℝ, 0 < ε ∧
      ∃ flow : (P × V) × ℝ → V,
        ContinuousOn flow (closedBall (p₀, 0) r ×ˢ Ioo (-ε) ε) ∧
        ∀ q ∈ closedBall (p₀, 0) r, flow (q, 0) = 0 ∧
          ∀ t ∈ Ioo (-ε) ε,
            HasDerivAt (fun τ => flow (q, τ))
              (fderiv ℝ (fun y => m (q.1, (flow (q, t), y))) 0 q.2) t :=
  ParametricFlow.Abelian.exists_continuous_parametric_flow_zero (multiplicationField m) (p₀, 0)
    (multiplicationField_contDiffAt m p₀ hm)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.MultiplicationFieldFlow.Abelian
