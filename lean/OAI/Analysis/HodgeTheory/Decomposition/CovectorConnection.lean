import OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential
import Mathlib.Analysis.Calculus.FDeriv.ContinuousAlternatingMap

/-! # Covector Connection -/

namespace OAI.Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions

noncomputable section

/-! The induced connection on genuine alternating covectors. Torsion-free
coefficients cancel under alternation, recovering the actual exterior derivative. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def covectorInfinitesimalAction (n : ℕ) (A : E →L[ℝ] E) : DifferentialForms.Manifold.Basic.FormValue E n →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n :=
  (ContinuousAlternatingMap.fderivCompContinuousLinearMapCLM ℂ (ContinuousLinearMap.id ℝ E)).flip A

theorem covectorInfinitesimalAction_apply (n : ℕ) (A : E →L[ℝ] E) (a : DifferentialForms.Manifold.Basic.FormValue E n) (v : Fin n → E) :
    covectorInfinitesimalAction n A a v = ∑ i, a (Function.update v i (A (v i))) := by
  change a.fderivCompContinuousLinearMap (ContinuousLinearMap.id ℝ E) A v = _
  rw [ContinuousAlternatingMap.fderivCompContinuousLinearMap_apply]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [Function.update_of_ne hj]

def covectorConnectionDerivative (n : ℕ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) (x : E) : E →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n :=
  fderiv ℝ a x - ((a x).fderivCompContinuousLinearMap (ContinuousLinearMap.id ℝ E)).comp (Γ x)

theorem covectorConnectionDerivative_apply (n : ℕ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) (x u : E) :
    covectorConnectionDerivative n Γ a x u = fderiv ℝ a x u - covectorInfinitesimalAction n (Γ x u) (a x) := rfl

theorem covectorConnectionDerivative_alternation (n : ℕ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) (x : E) (hΓ : ∀ u v, Γ x u v = Γ x v u) :
    ContinuousAlternatingMap.alternatizeUncurryFin (covectorConnectionDerivative n Γ a x) = extDeriv a x := by
  change ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ
    (fderiv ℝ a x - ((a x).fderivCompContinuousLinearMap (ContinuousLinearMap.id ℝ E)).comp (Γ x)) = _
  rw [map_sub]
  have hz := ContinuousAlternatingMap.alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero
    (a x) (ContinuousLinearMap.id ℝ E) hΓ
  change ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ a x) -
    ContinuousAlternatingMap.alternatizeUncurryFin
      ((a x).fderivCompContinuousLinearMap (ContinuousLinearMap.id ℝ E) |>.comp (Γ x)) = _
  rw [hz, sub_zero]
  rfl

end

end OAI.Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions
