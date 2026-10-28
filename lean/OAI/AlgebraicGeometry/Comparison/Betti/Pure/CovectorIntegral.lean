import OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorComplexEquiv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Covector Integral -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorIntegral.Holomorphic

noncomputable section

/-! Interval integration preserves the actual pure holomorphic covector subspace. -/

open _root_.MeasureTheory
open scoped Interval

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  {n : ℕ}

theorem pureCovector_intervalIntegral (f : ℝ → E [⋀^Fin n]→L[ℝ] ℂ) (a b : ℝ)
    (hf : ∀ t ∈ Set.uIcc a b, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 (f t)) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 (∫ t in a..b, f t) := by
  by_cases hi : IntervalIntegrable f volume a b
  · have he (v : Fin n → E) : (∫ t in a..b, f t) v = ∫ t in a..b, f t v :=
      ((ContinuousAlternatingMap.apply ℝ E ℂ v).intervalIntegral_comp_comm hi).symm
    intro z v
    change Fin n → E at v
    change (∫ t in a..b, f t) (fun i => (z : ℂ) • v i) =
      Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter n 0 z * (∫ t in a..b, f t) v
    rw [he, he, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr (fun t ht => hf t ht z v)
  · rw [intervalIntegral.integral_undef hi]
    exact (Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule E n 0).zero_mem

end

end OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorIntegral.Holomorphic
