import OAI.AlgebraicTopology.DeRham.Comparison.RadialOne
import OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts

/-! # Antiholomorphic Contraction -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicContraction.Dolbeault

noncomputable section

/-! Actual contraction of alternating covectors, and its antiholomorphic
part in the tangent direction. Both operators are complex-linear in forms. -/

open _root_.ContinuousAlternatingMap

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

def covectorContraction (n : ℕ) (v : E) :
    (E [⋀^Fin (n + 1)]→L[ℝ] ℂ) →L[ℂ] (E [⋀^Fin n]→L[ℝ] ℂ) where
  toFun a := a.curryLeft v
  map_add' a b := by ext w; rfl
  map_smul' c a := by ext w; rfl
  cont :=
    (((curryLeftLI : (E [⋀^Fin (n + 1)]→L[ℝ] ℂ) →ₗᵢ[ℝ]
      (E →L[ℝ] E [⋀^Fin n]→L[ℝ] ℂ)).toContinuousLinearMap).flip v).continuous

theorem covectorContraction_apply (n : ℕ) (v : E)
    (a : E [⋀^Fin (n + 1)]→L[ℝ] ℂ) (w : Fin n → E) :
    covectorContraction n v a w = a (Fin.cons v w) := rfl

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def antiContraction (n : ℕ) (v : E) :
    (E [⋀^Fin (n + 1)]→L[ℝ] ℂ) →L[ℂ] (E [⋀^Fin n]→L[ℝ] ℂ) :=
  (1 / 2 : ℂ) • (covectorContraction n v + Complex.I • covectorContraction n (Complex.I • v))

theorem antiContraction_eq_projected (n : ℕ) (v : E)
    (a : E [⋀^Fin (n + 1)]→L[ℝ] ℂ) :
    antiContraction n v a = Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (E [⋀^Fin n]→L[ℝ] ℂ) a.curryLeft v := rfl

theorem antiContraction_smul_direction (n : ℕ) (z : ℂ) (v : E)
    (a : E [⋀^Fin (n + 1)]→L[ℝ] ℂ) :
    antiContraction n (z • v) a = (star z) • antiContraction n v a :=
  Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply_smul E (E [⋀^Fin n]→L[ℝ] ℂ) a.curryLeft z v

omit [IsScalarTower ℝ ℂ E] in
theorem antiContraction_apply (n : ℕ) (v : E)
    (a : E [⋀^Fin (n + 1)]→L[ℝ] ℂ) (w : Fin n → E) :
    antiContraction n v a w =
      (1 / 2 : ℂ) * (a (Fin.cons v w) + Complex.I * a (Fin.cons (Complex.I • v) w)) := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.AntiholomorphicContraction.Dolbeault
