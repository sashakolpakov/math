import OAI.AlgebraicGeometry.Comparison.Betti.CauchyParameterCoefficients

/-! # Cauchy Polynomials -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Smooth.CauchyPolynomials.Dolbeault

noncomputable section

/-! The original Cauchy partial sums are jointly smooth in real parameters
and the complex variable. Their actual parameter derivatives are the
same partial sums of the actual parameter derivative of the input. -/

open Set _root_.Metric
open scoped ContDiff

variable {P F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

def cauchyParameterPolynomial (g : P × ℂ → F) (c : ℂ) (r : ℝ) (N : ℕ) (q : P × ℂ) : F :=
  (cauchyPowerSeries (fun z => g (q.1, z)) c r).partialSum N q.2

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] in
theorem cauchyParameterPolynomial_eq_sum (g : P × ℂ → F)
    (c : ℂ) (r : ℝ) (N : ℕ) (q : P × ℂ) :
    cauchyParameterPolynomial g c r N q =
      ∑ n ∈ Finset.range N, q.2 ^ n • CauchyParameterCoefficients.Dolbeault.cauchyParameterCoefficient g c r n q.1 := by
  simp only [cauchyParameterPolynomial, FormalMultilinearSeries.partialSum,
    CauchyParameterCoefficients.Dolbeault.cauchyPowerSeries_eq_parameterCoefficient]

variable [FiniteDimensional ℝ P]

theorem cauchyParameterPolynomial_smooth {g : P × ℂ → F} {W : Set (P × ℂ)}
    (hW : IsOpen W) (hg : ContDiffOn ℝ ∞ g W) {S : Set P} (hS : IsOpen S)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hSW : S ×ˢ sphere c r ⊆ W) (N : ℕ) :
    ContDiffOn ℝ ∞ (cauchyParameterPolynomial g c r N) (S ×ˢ univ) := by
  have he : cauchyParameterPolynomial g c r N =
      fun q : P × ℂ => ∑ n ∈ Finset.range N,
        q.2 ^ n • CauchyParameterCoefficients.Dolbeault.cauchyParameterCoefficient g c r n q.1 :=
    funext (cauchyParameterPolynomial_eq_sum g c r N)
  rw [he]
  apply ContDiffOn.sum
  intro n hn
  exact (contDiffOn_snd.pow n).smul
    ((CauchyParameterCoefficients.Dolbeault.cauchyParameterCoefficient_smooth hW hg hS hr hSW n).comp
      contDiffOn_fst (fun q hq => hq.1))

theorem hasFDerivAt_cauchyParameterPolynomial {g : P × ℂ → F} {W : Set (P × ℂ)}
    (hW : IsOpen W) (hg : ContDiffOn ℝ ∞ g W) {S : Set P} (hS : IsOpen S)
    {p : P} (hp : p ∈ S) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hSW : S ×ˢ sphere c r ⊆ W) (N : ℕ) (w : ℂ) :
    HasFDerivAt (fun q => cauchyParameterPolynomial g c r N (q, w))
      (cauchyParameterPolynomial (ContourDerivative.Dolbeault.circleParameterDerivative g) c r N (p, w)) p := by
  simp_rw [cauchyParameterPolynomial_eq_sum]
  exact HasFDerivAt.fun_sum (fun n _ =>
    (CauchyParameterCoefficients.Dolbeault.hasFDerivAt_cauchyParameterCoefficient hW hg hS hp hr hSW n).const_smul (w ^ n))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Smooth.CauchyPolynomials.Dolbeault
