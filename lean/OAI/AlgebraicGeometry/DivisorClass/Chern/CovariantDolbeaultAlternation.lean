import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.ConnectionSymbols
import OAI.Analysis.DifferentialForms.Manifold.DolbeaultLocal

/-! # Covariant Dolbeault Alternation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CovariantDolbeaultAlternation

noncomputable section

/-! The antiholomorphic alternation of the genuine line covector connection is the original Dolbeault derivative. -/

open _root_.ContinuousAlternatingMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

theorem alternation_complexAntilinearPart (n : ℕ) (D : E →L[ℝ] Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) D) =
      (1 / 2 : ℂ) • (alternatizeUncurryFin D + Complex.I •
        alternatizeUncurryFin (D.comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I))) := by
  have he : Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) D =
      (1 / 2 : ℂ) • (D + Complex.I • D.comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)) := by
    ext v w
    rfl
  rw [he, alternatizeUncurryFin_smul, alternatizeUncurryFin_add, alternatizeUncurryFin_smul]

theorem covectorConnectionDerivative_antilinear_alternation (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E)
    (hG : ∀ v w, G x v w = G x w v)
    (hGJ : ∀ v w, G x (Complex.I • v) w = G x (Complex.I • w) v) :
    alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
      (Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorConnectionDerivative n G a x)) = Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime a x := by
  let C := ((a x).fderivCompContinuousLinearMap (ContinuousLinearMap.id ℝ E)).comp (G x)
  have hc : alternatizeUncurryFin C = 0 :=
    alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero (a x) (ContinuousLinearMap.id ℝ E) hG
  have hcJ : alternatizeUncurryFin (C.comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I)) = 0 := by
    change alternatizeUncurryFin (((a x).fderivCompContinuousLinearMap (ContinuousLinearMap.id ℝ E)).comp
      ((G x).comp (ContinuousLinearMap.lsmul ℝ ℂ Complex.I))) = 0
    exact alternatizeUncurryFin_fderivCompContinuousLinearMap_eq_zero (a x) (ContinuousLinearMap.id ℝ E) hGJ
  have hz : alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) C) = 0 := by
    rw [alternation_complexAntilinearPart, hc, hcJ, smul_zero, add_zero, smul_zero]
  change alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (fderiv ℝ a x - C)) = _
  rw [map_sub]
  change alternatizeUncurryFinCLM ℝ E ℂ
    (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (fderiv ℝ a x) - Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) C) = _
  rw [map_sub]
  change Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime a x - alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) C) = _
  rw [hz, sub_zero]

theorem lineConnectionTerm_antilinear_zero (n : ℕ) (A : E →L[ℝ] ℂ) (a : Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    (hA : ∀ v, A (Complex.I • v) = Complex.I * A v) :
    Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (Line.ConnectionSymbols.lineConnectionTerm n A a) = 0 := by
  ext v w
  rw [Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM_apply, Line.ConnectionSymbols.lineConnectionTerm_apply, Line.ConnectionSymbols.lineConnectionTerm_apply, hA]
  simp only [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply, smul_eq_mul]
  change (1 / 2 : ℂ) * (A v * a w + Complex.I * ((Complex.I * A v) * a w)) = 0
  calc
    _ = (1 / 2 : ℂ) * (A v * a w + Complex.I ^ 2 * (A v * a w)) := by ring
    _ = 0 := by rw [Complex.I_sq]; ring

theorem lineCovectorConnectionDerivative_antilinear_alternation (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (x : E)
    (hG : ∀ v w, G x v w = G x w v)
    (hGJ : ∀ v w, G x (Complex.I • v) w = G x (Complex.I • w) v)
    (hA : ∀ v, A x (Complex.I • v) = Complex.I * A x v) :
    alternatizeUncurryFin (Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E (Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
      (Line.ConnectionSymbols.lineCovectorConnectionDerivative n G A a x)) = Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime a x := by
  rw [Line.ConnectionSymbols.lineCovectorConnectionDerivative, map_add, lineConnectionTerm_antilinear_zero n (A x) (a x) hA, add_zero]
  exact covectorConnectionDerivative_antilinear_alternation n G a x hG hGJ

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CovariantDolbeaultAlternation
