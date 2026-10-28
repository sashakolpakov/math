import OAI.NumberTheory.Quaternion.Arithmetic.AdelicCompact
import OAI.NumberTheory.Quaternion.Arithmetic.AmbientProjection
import OAI.NumberTheory.Quaternion.Arithmetic.StrongApproximationReduction
import OAI.NumberTheory.Quaternion.Arithmetic.SplitAdeles

/-! # Strong Approximation -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.StrongApproximation

noncomputable section

/-! Strong approximation for the actual regular quaternion norm-one
matrix group. The nonsplit case uses the constructed compact adelic
quotient and its invariant S-arithmetic quotient measures. -/

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem quaternion_nonsplit_arithmetic_volume (a b : F) (ha : a ≠ 0)
    (hs : ¬ ∃ x y : F, x ^ 2 - a * y ^ 2 = b)
    (S : Finset (LocalAdeles.Place F)) (harch : ∀ v : NumberField.InfinitePlace F, Sum.inl v ∈ S)
    (T : Finset (ApproximationTopology.AwayPlace S)) :
    CompactQuotientProjection.QuotientHasInvariantProbability (Ambient.arithmeticAmbientSubgroup (MatrixGroup.quaternionNormOneMatrixGroup a b) S T) := by
  let : CompactSpace (AdelicGroup.FullAdelicGroupPoints (MatrixGroup.quaternionNormOneMatrixGroup a b) ⧸
      (AdelicGroup.diagonalFullAdelic (MatrixGroup.quaternionNormOneMatrixGroup a b)).range) :=
    AdelicCompact.quaternion_nonsplit_adelic_quotient_compact a b ha hs
  exact AmbientProjection.arithmeticAmbient_quotientProbability_of_full (MatrixGroup.quaternionNormOneMatrixGroup a b) S harch T

theorem strongApproximation_quaternion (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (S : Finset (LocalAdeles.Place F)) (harch : ∀ v : NumberField.InfinitePlace F, Sum.inl v ∈ S)
    (hnoncompact : ∃ v : LocalAdeles.Place F, v ∈ S ∧ ¬ CompactSpace (LocalAdeles.LocalPoints (MatrixGroup.quaternionNormOneMatrixGroup a b) v)) :
    DenseRange (LocalAdeles.diagonalAway (MatrixGroup.quaternionNormOneMatrixGroup a b) S) := by
  by_cases hs : ∃ x y : F, x ^ 2 - a * y ^ 2 = b
  · obtain ⟨x, y, hxy⟩ := hs
    exact SplitAdeles.strongApproximation_splitQuaternion a b x y ha hb hxy S harch
  · exact StrongApproximationReduction.strongApproximation_quaternion_of_volume a b ha hb S harch hnoncompact
      (quaternion_nonsplit_arithmetic_volume a b ha hs S harch)

end

end OAI.NumberTheory.Quaternion.Arithmetic.StrongApproximation
