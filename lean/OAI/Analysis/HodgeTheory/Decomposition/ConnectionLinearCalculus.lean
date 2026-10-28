import OAI.Analysis.HodgeTheory.Decomposition.CovectorConnection

/-! # Connection Linear Calculus -/

namespace OAI.Analysis.HodgeTheory.Decomposition.ConnectionLinearCalculus.Constructions

noncomputable section

/-! Finite sums and real constant multiples for the genuine induced
connection, with differentiability hypotheses used only for calculus. -/

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

theorem covectorConnectionDerivative_sum (n : ℕ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (a : ι → E → DifferentialForms.Manifold.Basic.FormValue E n) {x : E} (ha : ∀ i, DifferentiableAt ℝ (a i) x) (u : E) :
    CovectorConnection.Constructions.covectorConnectionDerivative n Γ (fun y => ∑ i, a i y) x u =
      ∑ i, CovectorConnection.Constructions.covectorConnectionDerivative n Γ (a i) x u := by
  simp only [CovectorConnection.Constructions.covectorConnectionDerivative_apply]
  rw [fderiv_fun_sum (fun i _ => ha i), sum_apply, map_sum, Finset.sum_sub_distrib]

omit [Fintype ι] in
theorem covectorConnectionDerivative_real_smul (n : ℕ) (Γ : E → E →L[ℝ] E →L[ℝ] E)
    (a : E → DifferentialForms.Manifold.Basic.FormValue E n) {x : E} (ha : DifferentiableAt ℝ a x) (r : ℝ) (u : E) :
    CovectorConnection.Constructions.covectorConnectionDerivative n Γ (fun y => r • a y) x u =
      r • CovectorConnection.Constructions.covectorConnectionDerivative n Γ a x u := by
  simp only [CovectorConnection.Constructions.covectorConnectionDerivative_apply]
  have h : fderiv ℝ (fun y => r • a y) x = r • fderiv ℝ a x := by
    convert! (ha.hasFDerivAt.const_smul r).fderiv using 1
  rw [h, smul_apply, map_smul, smul_sub]

end

end OAI.Analysis.HodgeTheory.Decomposition.ConnectionLinearCalculus.Constructions
