import OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingExponentialSubgroup
import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalSymmetricExponential

/-! # Commuting Exponential Homeomorph -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingExponentialHomeomorph.Construction

noncomputable section

/-! A commuting symmetric subspace is homeomorphic, by exponentiation,
to its closed split subgroup, and the exponential homomorphism is faithful. -/

open NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem commutingExponentialHom_injective
    (a : Submodule ℝ (L →L[ℝ] L)) (ha : ∀ X ∈ a, X.toLinearMap.IsSymmetric)
    (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) : Function.Injective (CommutingExponentialSubgroup.Construction.commutingExponentialHom a hc) := by
  apply (injective_iff_map_eq_one (CommutingExponentialSubgroup.Construction.commutingExponentialHom a hc)).mpr
  intro X hX
  have he : exp X.toAdd.val = 1 := congrArg Units.val hX
  have hz : X.toAdd.val = 0 := OrthogonalSymmetricExponential.Construction.symmetric_exponential_orthogonal_eq_zero X.toAdd.val
    (ha X.toAdd.val X.toAdd.property) (by intro x y; rw [he]; rfl)
  apply Multiplicative.toAdd.injective
  exact Subtype.ext hz

theorem commuting_symmetric_exponential_isEmbedding
    (a : Submodule ℝ (L →L[ℝ] L)) (ha : ∀ X ∈ a, X.toLinearMap.IsSymmetric)
    (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) :
    Topology.IsEmbedding (fun X : a => OperatorExponentialUnits.Construction.operatorExpUnit X.val) := by
  have hp := CommutingExponentialSubgroup.Construction.symmetric_subspace_exponential_isProperMap a ha
  have hi : Function.Injective (fun X : a => OperatorExponentialUnits.Construction.operatorExpUnit X.val) := by
    intro X Y hXY
    have he := commutingExponentialHom_injective a ha hc
      (show CommutingExponentialSubgroup.Construction.commutingExponentialHom a hc (Multiplicative.ofAdd X) =
        CommutingExponentialSubgroup.Construction.commutingExponentialHom a hc (Multiplicative.ofAdd Y) from hXY)
    exact congrArg Multiplicative.toAdd he
  exact (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
    hp.continuous hi hp.isClosedMap).isEmbedding

def commutingExponentialHomeomorph
    (a : Submodule ℝ (L →L[ℝ] L)) (ha : ∀ X ∈ a, X.toLinearMap.IsSymmetric)
    (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) : a ≃ₜ CommutingExponentialSubgroup.Construction.commutingExponentialSubgroup a hc := by
  change a ≃ₜ Set.range (fun X : a => OperatorExponentialUnits.Construction.operatorExpUnit X.val)
  exact (commuting_symmetric_exponential_isEmbedding a ha hc).toHomeomorph

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingExponentialHomeomorph.Construction
