import OAI.AlgebraicGeometry.Comparison.Betti.Pure.CoefficientDerivative
import OAI.Analysis.DifferentialForms.Manifold.DolbeaultCoefficientType
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! # Coefficient Criterion -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientCriterion

noncomputable section

/-! The genuine pure-form derivative condition is the Cauchy–Riemann condition on coefficients. -/

open Filter
open scoped _root_.Topology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {n : ℕ} {F : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm E n} {x : E}

theorem pureForm_differentiableAt_complex (hF : DifferentiableAt ℝ F x)
    (hP : ∀ᶠ y in 𝓝 x, OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 (F y))
    (hExt : OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E (n + 1) 0 (extDeriv F x)) : DifferentiableAt ℂ F x := by
  let D := Pure.CoefficientDerivative.Holomorphic.pureCoefficientDerivativeComplex (fderiv ℝ F x)
    (OAI.Analysis.DifferentialForms.Manifold.DolbeaultCoefficientType.fderiv_hasBidegree hF hP) hExt
  have he : D.restrictScalars ℝ = fderiv ℝ F x := by
    ext u
    rfl
  exact (hasFDerivAt_of_restrictScalars ℝ hF.hasFDerivAt he).differentiableAt

theorem pureForm_extDeriv_pure_of_complex (hF : DifferentiableAt ℂ F x)
    (hP : ∀ᶠ y in 𝓝 x, OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 (F y)) :
    OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E (n + 1) 0 (extDeriv F x) := by
  have hD := OAI.Analysis.DifferentialForms.Manifold.DolbeaultCoefficientType.fderiv_hasBidegree (hF.restrictScalars ℝ) hP
  intro z v
  change Fin (n + 1) → E at v
  change ContinuousAlternatingMap.alternatizeUncurryFin (fderiv ℝ F x)
      (fun i => (z : ℂ) • v i) = OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter (n + 1) 0 z * extDeriv F x v
  have hfirst (u : E) : fderiv ℝ F x ((z : ℂ) • u) = (z : ℂ) • fderiv ℝ F x u := by
    rw [hF.fderiv_restrictScalars ℝ]
    exact (fderiv ℂ F x).map_smul (z : ℂ) u
  have hrest (u : E) (w : Fin n → E) :
      fderiv ℝ F x u (fun i => (z : ℂ) • w i) = (z : ℂ) ^ n * fderiv ℝ F x u w := by
    have h := hD u z w
    change fderiv ℝ F x u (fun i => (z : ℂ) • w i) =
      OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter n 0 z * fderiv ℝ F x u w at h
    simpa only [OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_zero, mul_one] using h
  rw [OAI.Analysis.DifferentialForms.Manifold.DolbeaultCoefficientType.alternatizeUncurryFin_scaling (fderiv ℝ F x) (z : ℂ) (z : ℂ) ((z : ℂ) ^ n)
    hfirst hrest]
  simp only [OAI.Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_zero, mul_one, pow_succ, extDeriv]
  ring

theorem pureForm_extDeriv_pure_iff (hF : DifferentiableAt ℝ F x)
    (hP : ∀ᶠ y in 𝓝 x, OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 (F y)) :
    OAI.Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E (n + 1) 0 (extDeriv F x) ↔ DifferentiableAt ℂ F x :=
  ⟨pureForm_differentiableAt_complex hF hP, fun h => pureForm_extDeriv_pure_of_complex h hP⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoefficientCriterion
