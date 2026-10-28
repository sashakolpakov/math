import OAI.AlgebraicGeometry.Comparison.Betti.Pure.CovectorComplexEquiv
import OAI.AlgebraicTopology.DeRham.Comparison.RadialOne

/-! # Coefficient Derivative -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Pure.CoefficientDerivative.Holomorphic

noncomputable section

/-! The pure exterior derivative determines complex linearity of actual coefficient derivatives. -/

open _root_.ContinuousAlternatingMap

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] {n : ℕ}

theorem pureCovector_curryLeft_smul (ω : E [⋀^Fin (n + 1)]→L[ℝ] ℂ)
    (hω : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E (n + 1) 0 ω) (z : ℂ) (x : E) :
    ω.curryLeft (z • x) = z • ω.curryLeft x := by
  ext v
  let P := CovectorComplexEquiv.Holomorphic.pureCovectorComplexMultilinearMap ω hω
  have h := P.map_update_smul (Fin.cons x v) (0 : Fin (n + 1)) z x
  simp only [Fin.update_cons_zero, smul_eq_mul] at h
  exact h

theorem pureCoefficientDerivative_succ_map_smul
    (D : E →L[ℝ] E [⋀^Fin (n + 1)]→L[ℝ] ℂ)
    (hD : ∀ x, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E (n + 1) 0 (D x))
    (hAlt : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E (n + 2) 0 (alternatizeUncurryFin D)) (z : ℂ) (x : E) :
    D (z • x) = z • D x := by
  have hc : AlgebraicTopology.DeRham.Comparison.RadialOne.contractionDerivative D (z • x) =
      z • AlgebraicTopology.DeRham.Comparison.RadialOne.contractionDerivative D x := by
    ext y v
    exact congrArg (fun ω : E [⋀^Fin n]→L[ℝ] ℂ => ω v)
      (pureCovector_curryLeft_smul (D y) (hD y) z x)
  have h := AlgebraicTopology.DeRham.Comparison.RadialOne.alternatize_contractionDerivative_add D (z • x)
  rw [hc, alternatizeUncurryFin_smul, pureCovector_curryLeft_smul _ hAlt,
    ← smul_add, AlgebraicTopology.DeRham.Comparison.RadialOne.alternatize_contractionDerivative_add] at h
  exact h.symm

theorem pureCoefficientDerivative_zero_map_smul
    (D : E →L[ℝ] E [⋀^Fin 0]→L[ℝ] ℂ)
    (hAlt : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 0 (alternatizeUncurryFin D)) (z : ℂ) (x : E) :
    D (z • x) = z • D x := by
  ext v
  have he (y : E) : (alternatizeUncurryFin D).curryLeft y v = D y v := by
    simp only [curryLeft_apply_apply, alternatizeUncurryFin_apply, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Fin.val_zero, pow_zero, one_smul]
    simp
  have h := congrArg (fun ω : E [⋀^Fin 0]→L[ℝ] ℂ => ω v)
    (pureCovector_curryLeft_smul (alternatizeUncurryFin D) hAlt z x)
  change (alternatizeUncurryFin D).curryLeft (z • x) v =
    z • ((alternatizeUncurryFin D).curryLeft x v) at h
  rw [he, he] at h
  exact h

theorem pureCoefficientDerivative_map_smul
    (D : E →L[ℝ] E [⋀^Fin n]→L[ℝ] ℂ)
    (hD : ∀ x, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 (D x))
    (hAlt : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E (n + 1) 0 (alternatizeUncurryFin D)) (z : ℂ) (x : E) :
    D (z • x) = z • D x := by
  cases n with
  | zero => exact pureCoefficientDerivative_zero_map_smul D hAlt z x
  | succ n => exact pureCoefficientDerivative_succ_map_smul D hD hAlt z x

def pureCoefficientDerivativeComplex
    (D : E →L[ℝ] E [⋀^Fin n]→L[ℝ] ℂ)
    (hD : ∀ x, Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E n 0 (D x))
    (hAlt : Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E (n + 1) 0 (alternatizeUncurryFin D)) :
    E →L[ℂ] E [⋀^Fin n]→L[ℝ] ℂ where
  toFun := D
  map_add' := D.map_add
  map_smul' z x := pureCoefficientDerivative_map_smul D hD hAlt z x
  cont := D.cont

end

end OAI.AlgebraicGeometry.Comparison.Betti.Pure.CoefficientDerivative.Holomorphic
