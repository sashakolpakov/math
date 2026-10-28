import OAI.AlgebraicGeometry.Comparison.Betti.CauchyPolynomialDirections

/-! # Cauchy Polynomial Parameter Jets -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.CauchyPolynomialParameterJets.Dolbeault

noncomputable section

/-! All actual iterated parameter derivatives commute with the original
Cauchy partial sum. Directions are embedded in the parameter factor of
the original joint domain. -/

open Set _root_.Metric
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
  [CompleteSpace F]

omit [CompleteSpace F] in
theorem cauchyParameterPolynomial_contDiff {g : P × ℂ → F} (hg : ContDiff ℝ ∞ g)
    (c : ℂ) {r : ℝ} (hr : 0 < r) (N : ℕ) :
    ContDiff ℝ ∞ (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g c r N) := by
  have h := Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial_smooth (c := c) isOpen_univ hg.contDiffOn isOpen_univ hr
    (subset_univ _) N
  exact contDiffOn_univ.mp (by simpa only [univ_prod_univ] using h)

theorem cauchyParameterPolynomial_parameter_jet {g : P × ℂ → F} (hg : ContDiff ℝ ∞ g)
    (c : ℂ) {r : ℝ} (hr : 0 < r) (N k : ℕ) (v : Fin k → P) (q : P × ℂ) :
    iteratedFDeriv ℝ k (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g c r N) q (fun i => (v i, 0)) =
      Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial
        (fun y => iteratedFDeriv ℝ k g y (fun i => (v i, 0))) c r N q := by
  have hpoly := cauchyParameterPolynomial_contDiff hg c hr N
  induction k generalizing q with
  | zero => simp only [iteratedFDeriv_zero_apply]
  | succ k ih =>
    let u : Fin k → P × ℂ := fun i => (Fin.tail v i, 0)
    let G : P × ℂ → F := fun y => iteratedFDeriv ℝ k g y u
    have hG : ContDiff ℝ ∞ G :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => P × ℂ) F u).contDiff.comp
        (hg.iteratedFDeriv_right (m := ∞)
          (WithTop.coe_le_coe.mpr (le_top : (⊤ : ℕ∞) + (k : ℕ∞) ≤ ⊤)))
    have hDp := (hpoly.contDiffAt (x := q)).differentiableAt_iteratedFDeriv
      (m := k) (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))
    rw [hDp.iteratedFDeriv_succ_apply_left']
    have he : (fun y => iteratedFDeriv ℝ k (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g c r N) y u) =
        Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial G c r N := funext (fun y => ih (Fin.tail v) y)
    change fderiv ℝ (fun y => iteratedFDeriv ℝ k (Smooth.CauchyPolynomials.Dolbeault.cauchyParameterPolynomial g c r N) y u)
      q (v 0, 0) = _
    rw [he, CauchyPolynomialDirections.Dolbeault.cauchyParameterPolynomial_parameter_fderiv isOpen_univ hG.contDiffOn isOpen_univ
      (mem_univ _) hr (subset_univ _) N (v 0)]
    have heG : (fun y => fderiv ℝ G y (v 0, 0)) =
        (fun y => iteratedFDeriv ℝ (k + 1) g y (fun i => (v i, 0))) := by
      funext y
      exact ((hg.contDiffAt (x := y)).differentiableAt_iteratedFDeriv
        (m := k) (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top k))).iteratedFDeriv_succ_apply_left'
          (m := fun i : Fin (k + 1) => (v i, (0 : ℂ))) |>.symm
    rw [heG]

end

end OAI.AlgebraicGeometry.Comparison.Betti.CauchyPolynomialParameterJets.Dolbeault
