import OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange
import OAI.AlgebraicGeometry.ComplexMultiplication.CMCore
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Class Descent -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Descent from the complex span of genuine algebraic classes

A rational class whose complex image lies in the complex span of actual
cycle classes is already a rational cycle class. This follows by scalar
extension of the quotient by the rational cycle-class image. The geometric
application uses the proved coefficient-comparison injectivity under finite
cohomological dimension; it requires no cycle-algebraicity hypothesis.
-/

open scoped TensorProduct

namespace ComplexMultiplication.ClassDescent.CM

/-- Extension of fields reflects membership in an arbitrary rational
subspace. The proof uses the actual quotient and faithful scalar extension. -/
theorem one_tmul_mem_baseChange_iff {K L U : Type*}
    [Field K] [Field L] [Algebra K L] [AddCommGroup U] [Module K U]
    (P : Submodule K U) (u : U) :
    (1 : L) ⊗ₜ[K] u ∈ P.baseChange L ↔ u ∈ P := by
  constructor
  · rintro ⟨x, hx⟩
    have hz : P.mkQ.comp P.subtype = 0 := by
      ext y
      simp
    have hbase : (P.mkQ.baseChange L).comp (P.subtype.baseChange L) = 0 := by
      rw [← LinearMap.baseChange_comp, hz, LinearMap.baseChange_zero]
    have hu : (1 : L) ⊗ₜ[K] P.mkQ u = 0 := by
      change P.mkQ.baseChange L ((1 : L) ⊗ₜ[K] u) = 0
      rw [← hx]
      exact DFunLike.congr_fun hbase x
    have hquot := (Module.FaithfullyFlat.one_tmul_eq_zero_iff K (U ⧸ P) (P.mkQ u)).mp hu
    exact (Submodule.Quotient.mk_eq_zero P).mp hquot
  · exact Submodule.tmul_mem_baseChange_of_mem 1

end ComplexMultiplication.ClassDescent.CM

/-- The complex span of the actual rational geometric cycle-class image,
mapped into ordinary complex singular cohomology by canonical coefficients. -/
def Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexGeometricAlgebraicClasses (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    Submodule ℂ (V.complexCohomology (p + p)) :=
  ((V.geometricAlgebraicClasses p).baseChange ℂ).map
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) (p + p))

/-- Passing to complex coefficients does not create new algebraic rational
classes. This is the final descent step needed after constructing complex
monomial lines in the geometric cycle-class span. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rational_mem_complexGeometricAlgebraicClasses_iff
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ)
    [Module.Finite ℚ (V.rationalCohomology (p + p))]
    (a : V.rationalCohomology (p + p)) :
    V.rationalCohomologyInclusion (p + p) a ∈ V.complexGeometricAlgebraicClasses p ↔
      a ∈ V.geometricAlgebraicClasses p := by
  have h : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) (p + p)
      ((1 : ℂ) ⊗ₜ[ℚ] a) ∈ V.complexGeometricAlgebraicClasses p ↔
      a ∈ V.geometricAlgebraicClasses p := by
    constructor
    · rintro ⟨x, hx, hxa⟩
      have heq : x = (1 : ℂ) ⊗ₜ[ℚ] a :=
        ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_injective (Betti.Scheme.schemePointSpace V.toOver) (p + p) hxa
      rw [heq] at hx
      exact (ComplexMultiplication.ClassDescent.CM.one_tmul_mem_baseChange_iff (V.geometricAlgebraicClasses p) a).mp hx
    · intro hx
      exact Submodule.mem_map.mpr
        ⟨(1 : ℂ) ⊗ₜ[ℚ] a, Submodule.tmul_mem_baseChange_of_mem 1 hx, rfl⟩
  simpa only [ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, one_smul] using! h

end

end OAI.AlgebraicGeometry
