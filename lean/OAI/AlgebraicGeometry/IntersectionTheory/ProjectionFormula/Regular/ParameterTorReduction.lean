import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.TorSpecialization
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.AnnihilatedParameterComplex

/-! # Parameter Tor Reduction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.ParameterTorReduction

noncomputable section

/-! If a regular parameter kills one module and is regular on the
other, reducing the ambient ring preserves every native Tor length. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

universe u

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Parameter.ScalarQuotient

variable (R : Type u) [CommRing R] (r : R) (hr : IsSMulRegular R r)
  (M N : ModuleCat.{u} R) (hM : ∀ m : M, r • m = 0) (hN : IsSMulRegular N r)

include hr hM hN

theorem length (n : ℕ) :
    Module.length (Parameter.ScalarQuotient.Ring R r)
      (((Tor (ModuleCat (Parameter.ScalarQuotient.Ring R r)) n).obj ((Parameter.ScalarQuotient.quotient R r).obj M)).obj ((Parameter.ScalarQuotient.quotient R r).obj N)) =
    Module.length R (((Tor (ModuleCat R) n).obj M).obj N) := by
  let P := projectiveResolution N
  let K := Parameter.TorSpecialization.tensorComplex R M N P
  have hK : ∀ i, ∀ m : K.X i, r • m = 0 :=
    fun i => AnnihilatedParameterComplex.tensor R r M (P.complex.X i) hM
  have h₁ := Parameter.TorSpecialization.length R r hr M N hN P n
  have h₂ := AnnihilatedParameterComplex.homology_length R r K hK n
  exact (h₁.trans h₂).trans (P.isoLeftDerivedObj (tensorLeft M) n).toLinearEquiv.length_eq.symm

theorem euler (d : ℕ) :
    ProjectionFormula.Tor.Euler.euler (Parameter.ScalarQuotient.Ring R r) ((Parameter.ScalarQuotient.quotient R r).obj M) ((Parameter.ScalarQuotient.quotient R r).obj N) d =
      ProjectionFormula.Tor.Euler.euler R M N d := by
  apply Finset.sum_congr rfl
  intro n _
  exact congrArg (fun l : ℕ∞ => (-1 : ℚ) ^ n * (l.toNat : ℚ)) (ParameterTorReduction.length R r hr M N hM hN n)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.ParameterTorReduction
