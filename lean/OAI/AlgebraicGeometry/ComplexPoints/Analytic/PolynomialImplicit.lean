import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Polynomial Implicit -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialImplicit

noncomputable section

/-!
# Local graphs of regular complex polynomial zero sets

These are analytic lemmas about actual polynomial evaluation on finite-dimensional
complex vector spaces. The regularity hypothesis is the invertibility of the
specified partial derivative. No assertion identifying that hypothesis with
scheme-theoretic smoothness is made in this file.
-/

open Filter
open scoped _root_.Topology ContDiff

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Evaluation of a multivariate complex polynomial is complex smooth of every
order, including the analytic order `ω`. -/
theorem contDiff_polynomial_eval (p : MvPolynomial ι ℂ) (n : ℕ∞ω) :
    ContDiff ℂ n (fun x : ι → ℂ => MvPolynomial.eval x p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa only [MvPolynomial.eval_C] using contDiff_const
  | add p q hp hq => simpa only [MvPolynomial.eval_add] using hp.add hq
  | mul_X p i hp =>
      simpa only [MvPolynomial.eval_mul, MvPolynomial.eval_X] using
        hp.mul (contDiff_apply ℂ ℂ i)

/-- Actual simultaneous evaluation, separating free and solved-for coordinates. -/
def splitPolynomialMap (P : κ → MvPolynomial (ι ⊕ κ) ℂ)
    (z : (ι → ℂ) × (κ → ℂ)) : κ → ℂ :=
  fun k => MvPolynomial.eval (Sum.elim z.1 z.2) (P k)

theorem contDiff_splitPolynomialMap (P : κ → MvPolynomial (ι ⊕ κ) ℂ)
    (n : ℕ∞ω) : ContDiff ℂ n (splitPolynomialMap P) := by
  apply contDiff_pi.mpr
  intro k
  apply (contDiff_polynomial_eval (P k) n).comp
  apply contDiff_pi.mpr
  intro i
  cases i with
  | inl i => exact (contDiff_apply ℂ ℂ i).comp contDiff_fst
  | inr i => exact (contDiff_apply ℂ ℂ i).comp contDiff_snd

/-- A regular polynomial zero set is locally the graph of a complex analytic
function. The pointwise smoothness is `ContDiffAt ℂ ω`, mathlib's analytic order.
Both existence on a neighbourhood and uniqueness inside a neighbourhood of the
base point are asserted, rather than merely a one-way parametrization. -/
theorem exists_polynomial_zero_graph
    (P : κ → MvPolynomial (ι ⊕ κ) ℂ)
    (u : (ι → ℂ) × (κ → ℂ))
    (hu : splitPolynomialMap P u = 0)
    (hreg : (fderiv ℂ (splitPolynomialMap P) u ∘L
      ContinuousLinearMap.inr ℂ (ι → ℂ) (κ → ℂ)).IsInvertible) :
    ∃ ψ : (ι → ℂ) → (κ → ℂ),
      ψ u.1 = u.2 ∧
      ContDiffAt ℂ ω ψ u.1 ∧
      (∀ᶠ x in 𝓝 u.1, splitPolynomialMap P (x, ψ x) = 0) ∧
      (∀ᶠ z in 𝓝 u, splitPolynomialMap P z = 0 ↔ ψ z.1 = z.2) := by
  have hP := (contDiff_splitPolynomialMap P ω).contDiffAt (x := u)
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  refine ⟨hP.implicitFunction hn hreg, hP.implicitFunction_apply_self hn hreg,
    hP.contDiffAt_implicitFunction hn hreg, ?_, ?_⟩
  · simpa only [hu] using hP.eventually_apply_implicitFunction hn hreg
  · simpa only [hu] using hP.eventually_apply_eq_iff_implicitFunction hn hreg

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialImplicit
