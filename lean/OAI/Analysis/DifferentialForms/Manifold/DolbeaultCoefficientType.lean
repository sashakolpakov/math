import OAI.Analysis.DifferentialForms.Manifold.Bidegree
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin

/-! # Dolbeault Coefficient Type -/

namespace OAI.Analysis.DifferentialForms.Manifold.DolbeaultCoefficientType

/-!
Differentiating the full scalar character of a pure differential form preserves
the character in its existing covector arguments. This is a local assertion:
the purity hypothesis is needed only on a neighborhood of the point.
-/

open Filter
open scoped _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  {p q : ℕ} {form : Basic.RawForm E (p + q)} {x : E}

/-- The Fréchet derivative preserves the scalar character in the pre-existing
covector slots, independently of its new differentiation slot. -/
theorem fderiv_hasBidegree
    (hform : DifferentiableAt ℝ form x)
    (hpure : ∀ᶠ y in 𝓝 x, Bidegree.HasBidegree E p q (form y)) (u : E) :
    Bidegree.HasBidegree E p q (fderiv ℝ form x u) := by
  intro z v
  let L : (E [⋀^Fin (p + q)]→L[ℝ] ℂ) →L[ℝ]
      (E [⋀^Fin (p + q)]→L[ℝ] ℂ) :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM
      (ContinuousLinearMap.lsmul ℝ ℂ (z : ℂ))
  have heq : (fun y => L (form y)) =ᶠ[𝓝 x]
      (fun y => Bidegree.bidegreeCharacter p q z • form y) := by
    filter_upwards [hpure] with y hy
    ext w
    exact hy z w
  have hleft := L.hasFDerivAt.comp x hform.hasFDerivAt
  have hright := (hform.hasFDerivAt.const_smul (Bidegree.bidegreeCharacter p q z)).congr_of_eventuallyEq heq
  have hderiv := hleft.unique hright
  exact congrArg (fun D : E →L[ℝ] E [⋀^Fin (p + q)]→L[ℝ] ℂ => D u v) hderiv

omit [IsScalarTower ℝ ℂ E] in
/-- Alternation multiplies the character in the differentiation slot by the
character in the remaining covector slots. -/
theorem alternatizeUncurryFin_scaling {n : ℕ}
    (D : E →L[ℝ] E [⋀^Fin n]→L[ℝ] ℂ) (z a b : ℂ)
    (hfirst : ∀ u : E, D (z • u) = a • D u)
    (hrest : ∀ (u : E) (v : Fin n → E),
      D u (fun i => z • v i) = b * D u v)
    (v : Fin (n + 1) → E) :
    ContinuousAlternatingMap.alternatizeUncurryFin D (fun i => z • v i) =
      (a * b) * ContinuousAlternatingMap.alternatizeUncurryFin D v := by
  simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (-1 : ℤ) ^ (i : ℕ) • D (z • v i) (fun j => z • i.removeNth v j) = _
  rw [hfirst, ContinuousAlternatingMap.smul_apply, hrest]
  simp only [smul_eq_mul, zsmul_eq_mul]
  ring

end OAI.Analysis.DifferentialForms.Manifold.DolbeaultCoefficientType
