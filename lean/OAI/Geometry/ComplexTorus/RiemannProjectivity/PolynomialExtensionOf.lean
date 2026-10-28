import OAI.Geometry.ComplexTorus.RiemannProjectivity.RemovableGlobal
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialGrowth
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Polynomial Extension Of -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.PolynomialExtensionOf.Constructions.PolynomialExtension

noncomputable section

/-!
# RiemannProjectivity: polynomial extension across an entire branch equation

A polynomial-growth bound supplies local boundedness at every exceptional
point. Holomorphic removability and gluing give an entire function, and
Liouville's polynomial-growth theorem identifies it with a multivariate
polynomial. No continuity on the exceptional set is an input.
-/

open Set
open scoped _root_.Topology

theorem exists_polynomial_extension {n d : ℕ} {f g : (Fin n → ℂ) → ℂ}
    (hg : Differentiable ℂ g) (hne : ∃ y, g y ≠ 0)
    (hf : ∀ x, g x ≠ 0 → DifferentiableAt ℂ f x) {C : ℝ}
    (hbound : ∀ x, g x ≠ 0 → ‖f x‖ ≤ C * (max 1 ‖x‖) ^ d) :
    ∃ P : MvPolynomial (Fin n) ℂ,
      (∀ x, g x ≠ 0 → MvPolynomial.eval x P = f x) ∧
      ∀ x, ‖MvPolynomial.eval x P‖ ≤ C * (max 1 ‖x‖) ^ d := by
  have hB : Continuous (fun x : Fin n → ℂ => C * (max 1 ‖x‖) ^ d) :=
    continuous_const.mul ((continuous_const.max continuous_norm).pow d)
  obtain ⟨F, hF, heq, hb⟩ :=
    RemovableGlobal.Constructions.GlobalRemovability.exists_entire_extension_of_continuous_bound hg hne hf hB hbound
  obtain ⟨P, hP⟩ := AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.PolynomialGrowth.Constructions.Growth.exists_mvPolynomial_of_growth n hF hb
  exact ⟨P, fun x hx => (hP x).trans (heq x hx), fun x => hP x ▸ hb x⟩

/-- An isolated cone vertex is removable under a polynomial-growth bound.
Agreement with the resulting polynomial holds on the entire punctured space. -/
theorem exists_polynomial_of_punctured_growth {n d : ℕ} {f : (Fin (n + 1) → ℂ) → ℂ}
    (hf : ∀ x, x ≠ 0 → DifferentiableAt ℂ f x) {C : ℝ}
    (hbound : ∀ x, x ≠ 0 → ‖f x‖ ≤ C * (max 1 ‖x‖) ^ d) :
    ∃ P : MvPolynomial (Fin (n + 1)) ℂ,
      (∀ x, x ≠ 0 → MvPolynomial.eval x P = f x) ∧
      ∀ x, ‖MvPolynomial.eval x P‖ ≤ C * (max 1 ‖x‖) ^ d := by
  let g : (Fin (n + 1) → ℂ) → ℂ := fun x => x 0
  have hg : Differentiable ℂ g := differentiable_apply 0
  have hne : ∃ x, g x ≠ 0 := ⟨fun _ => 1, one_ne_zero⟩
  have hxne : ∀ x, g x ≠ 0 → x ≠ 0 := by
    intro x hx hx0
    exact hx (by simp only [g, hx0, Pi.zero_apply])
  obtain ⟨P, heq, hb⟩ := exists_polynomial_extension hg hne
    (fun x hx => hf x (hxne x hx)) (fun x hx => hbound x (hxne x hx))
  refine ⟨P, ?_, hb⟩
  intro x hx
  exact RemovableGlobal.Constructions.GlobalRemovability.eq_at_of_nonflat
    (RemovableGlobal.Constructions.GlobalRemovability.nonflat_of_entire_nonzero hg hne x)
    P.continuous_eval.continuousAt (hf x hx).continuousAt (Filter.Eventually.of_forall heq)

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.PolynomialExtensionOf.Constructions.PolynomialExtension
