import OAI.AlgebraicGeometry.HilbertScheme.Presentations.KillVariables
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerPolynomialGrading

/-! # Integer Kill Variables -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerKillVariables.GradedHilbert

noncomputable section

/-! Setting complementary variables to zero preserves the actual integer polynomial grading. -/

open _root_.MvPolynomial

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerPolynomialGrading.GradedModules

universe u v w

variable {σ : Type v} {τ : Type w} [Fintype σ] [Fintype τ]
variable {R : Type u} [CommRing R] {f : σ → τ}

theorem killVariables_integer_homogeneous (hf : Function.Injective f) {d : ℤ}
    {p : MvPolynomial τ R} (hp : p ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading R d) :
    MvPolynomial.killCompl hf p ∈ WeightedFreeModules.GradedModules.polynomialIntegerGrading R d := by
  intro a ha
  have hcoeff : p.coeff (a.mapDomain f) ≠ 0 := by rwa [coeff_killCompl] at ha
  have hd := hp hcoeff
  rw [IntegerPolynomialGrading.GradedModules.integerWeight_eq_degree, Finsupp.degree_mapDomain] at hd
  change Finsupp.weight (fun _ : σ => (1 : ℤ)) a = d
  rw [IntegerPolynomialGrading.GradedModules.integerWeight_eq_degree]
  exact hd

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.IntegerKillVariables.GradedHilbert
