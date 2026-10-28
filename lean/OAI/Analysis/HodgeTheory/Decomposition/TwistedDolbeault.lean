import OAI.Analysis.HodgeTheory.Decomposition.CovectorSymbolAction
import OAI.Analysis.DifferentialForms.Manifold.DolbeaultLocal

/-! # Twisted Dolbeault -/

namespace OAI.Analysis.HodgeTheory.Decomposition.TwistedDolbeault.Constructions

noncomputable section

/-! The twisted exterior derivative is exactly i times the difference of
the actual local antiholomorphic and holomorphic derivatives. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

theorem complexDerivativeParts_twisted (n : ℕ) (D : E →L[ℝ] DifferentialForms.Manifold.Basic.FormValue E n) :
    Complex.I • (DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (DifferentialForms.Manifold.Basic.FormValue E n) D - DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E (DifferentialForms.Manifold.Basic.FormValue E n) D) =
      -D.comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) := by
  apply ContinuousLinearMap.ext
  intro u
  change Complex.I • (DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (DifferentialForms.Manifold.Basic.FormValue E n) D u -
    DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E (DifferentialForms.Manifold.Basic.FormValue E n) D u) = -D (Complex.I • u)
  rw [DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply, DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM_apply]
  have hs : (D u + Complex.I • D (Complex.I • u)) -
      (D u - Complex.I • D (Complex.I • u)) = (2 : ℂ) • (Complex.I • D (Complex.I • u)) := by module
  rw [← smul_sub, hs]
  simp only [smul_smul]
  have hc : Complex.I * ((1 / 2 : ℂ) * (2 * Complex.I)) = -1 := by
    ring_nf
    simp
  rw [hc]
  exact neg_one_smul ℂ (D (Complex.I • u))

theorem twistedExteriorDerivative_eq_dolbeault (n : ℕ) (a : E → DifferentialForms.Manifold.Basic.FormValue E n) (x : E) :
    CovectorSymbolAction.Constructions.twistedExteriorDerivative n (ContinuousLinearMap.lsmul ℝ ℂ Complex.I) a x =
      Complex.I • (DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime a x - DifferentialForms.Manifold.DolbeaultLocal.extDerivPrime a x) := by
  have h := congrArg ContinuousAlternatingMap.alternatizeUncurryFin
    (complexDerivativeParts_twisted n (fderiv ℝ a x))
  rw [ContinuousAlternatingMap.alternatizeUncurryFin_smul] at h
  change Complex.I • (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ)
    (DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (DifferentialForms.Manifold.Basic.FormValue E n) (fderiv ℝ a x) - DifferentialForms.Manifold.ComplexDerivativeParts.complexLinearPartCLM E (DifferentialForms.Manifold.Basic.FormValue E n) (fderiv ℝ a x)) =
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E ℂ)
      (-(fderiv ℝ a x).comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)) at h
  rw [map_sub, map_neg] at h
  exact h.symm

end

end OAI.Analysis.HodgeTheory.Decomposition.TwistedDolbeault.Constructions
