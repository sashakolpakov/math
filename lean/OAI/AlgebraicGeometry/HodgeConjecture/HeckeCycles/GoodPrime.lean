import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PairedCompletion
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Models

/-! # Good Prime -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GoodPrime.CM

noncomputable section

/-! The local good-prime clauses needed by TateComparison follow from the reduction
of the actual integral family and the source's conjugate-pair labels. -/

open scoped Classical TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PairedCompletion.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E]
  [IsGalois ℚ E] [NumberField.IsCMField E]
  {K : Type} [Field K] [NumberField K]
  (M : PELModuli.CMPoints.Models.RankThreePELModel E K) {q : ℕ} [Fact q.Prime]
  (j : M.QadicChoice q) (R : M.GoodIntegralReduction q j)

include R

omit [IsGalois ℚ E] in
theorem denominator_prime_to_q : Nat.Coprime q M.arithmetic.denominator := by
  have hunit : IsUnit (M.arithmetic.denominator : ZMod q) := by
    simpa only [map_natCast] using M.arithmetic.denominator_isUnit.map R.residue
  exact ((ZMod.isUnit_iff_coprime _ _).mp hunit).symm

/-- All five local clauses of the good-prime condition, before packaging
the integral family and correspondence covers into TateComparison's data record. -/
theorem good_prime_conditions (places : GeometricSource.CM.Places E)
    (hsplit : j.HasSplitCoordinates M.extendedEmbedding) (a : M.Family) :
    Function.Bijective (PairedCompletion.CM.pairedCompletion E j M.extendedEmbedding places) ∧
    (∀ (v : Fin places.count) (side : Bool) (x : NumberField.RingOfIntegers E),
      PairedCompletion.CM.pairedCharacter E j M.extendedEmbedding places (v, !side) x =
        PairedCompletion.CM.pairedCharacter E j M.extendedEmbedding places (v, side)
          (NumberField.IsCMField.ringOfIntegersComplexConj E x)) ∧
    Nat.Coprime q (M.level a) ∧ Nat.Coprime q M.arithmetic.denominator ∧
      Nat.Coprime q (∏ i, (M.datum a).polarizationType i) := by
  refine ⟨PairedCompletion.CM.pairedCompletion_bijective E j M.extendedEmbedding places hsplit,
    PairedCompletion.CM.pairedCharacter_conjugate E j M.extendedEmbedding places,
    R.levelPrimeToQ a, denominator_prime_to_q E M j R, ?_⟩
  exact (Nat.coprime_pow_right_iff (by decide : 0 < 2) _ _).mp
    (R.polarizationPrimeToQ a)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GoodPrime.CM
