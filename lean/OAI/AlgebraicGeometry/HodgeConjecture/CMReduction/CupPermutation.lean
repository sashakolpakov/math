import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.IteratedCup
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.ComplexOperations

/-! # Cup Permutation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CupPermutation.CM.Construction

noncomputable section

/-! The exterior comparison gives alternation of the literal complex H1
cup product, so reordering factors changes only its nonzero permutation sign. -/

open _root_.CategoryTheory
open scoped TensorProduct

variable {A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety}
  {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1)}
  (C : ComplexMultiplication.KnownExteriorCohomology.CM.AbelianExteriorComparison A H)

def h1CupAlternating (n : ℕ) :
    A.variety.complexCohomology 1 [⋀^Fin n]→ₗ[ℂ] A.variety.complexCohomology n :=
  ((C.complexMap n).comp
    (ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ (A.variety.rationalCohomology 1) n).symm.toLinearMap).compAlternatingMap
        ((exteriorPower.ιMulti ℂ n).compLinearMap
          (ComplexOperations.CM.Construction.projectiveComplexification A.variety 1).symm.toLinearMap)

theorem h1CupAlternating_apply (n : ℕ) (v : Fin n → A.variety.complexCohomology 1) :
    h1CupAlternating C n v = IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) n v := by
  change C.complexMap n
    ((ComplexMultiplication.ExteriorBaseChange.CM.exteriorBaseChangeEquiv ℂ (A.variety.rationalCohomology 1) n).symm
      (exteriorPower.ιMulti ℂ n
        (fun i => (ComplexOperations.CM.Construction.projectiveComplexification A.variety 1).symm (v i)))) = _
  rw [IteratedCup.CM.Construction.complexMap_exteriorProduct C n]
  apply congrArg (IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) n)
  funext i
  exact (ComplexOperations.CM.Construction.projectiveComplexification A.variety 1).apply_symm_apply (v i)

include C

theorem h1Cup_perm (n : ℕ) (v : Fin n → A.variety.complexCohomology 1)
    (σ : Equiv.Perm (Fin n)) :
    IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) n (v ∘ σ) =
      Equiv.Perm.sign σ • IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) n v := by
  rw [← h1CupAlternating_apply C n (v ∘ σ), ← h1CupAlternating_apply C n v]
  exact (h1CupAlternating C n).map_perm v σ

theorem h1Cup_perm_mem (p : ℕ) (v : Fin (p + p) → A.variety.complexCohomology 1)
    (σ : Equiv.Perm (Fin (p + p)))
    (hv : IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) (p + p) v ∈
      A.variety.complexGeometricAlgebraicClasses p) :
    IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) (p + p) (v ∘ σ) ∈
      A.variety.complexGeometricAlgebraicClasses p := by
  rw [h1Cup_perm C]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · simpa only [h, one_smul] using hv
  · rw [h]
    change (-1 : ℤ) • IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace A.toOver) (p + p) v ∈ _
    simpa using (A.variety.complexGeometricAlgebraicClasses p).neg_mem hv

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CupPermutation.CM.Construction
