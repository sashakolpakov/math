import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ActionOnAmbientPositive
import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.DerivationInvariantComplement

/-! # Invariant Complement -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! The intrinsic positive derivations admit one complement preserved
by every split conjugation, including the regular contracting flow. -/

open NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance Split.InvariantComplement.Construction.fullSplitComplementEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance Split.InvariantComplement.Construction.fullSplitComplementEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance Split.InvariantComplement.Construction.fullSplitComplementEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance

theorem KillingSplit.Construction.KillingSplitWeightData.positiveDerivationsInWeightRaising_invariant
    (d : KillingSplit.Construction.KillingSplitWeightData B) (A : d.subspace)
    (X : Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement))
    (hX : X ∈ Positive.DerivationInvariantComplement.Construction.positiveDerivationsInWeightRaising B d.basis d.regularElement.val
      (fun i => d.weight i d.regularElement)) :
    d.ambientPositiveConjugation A X ∈ Positive.DerivationInvariantComplement.Construction.positiveDerivationsInWeightRaising B d.basis
      d.regularElement.val (fun i => d.weight i d.regularElement) := by
  change (d.ambientPositiveConjugation A X).val ∈ DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val
  rw [d.ambientPositiveConjugation_val]
  rw [← d.positiveConjugation_val A ⟨X.val, hX⟩]
  exact (d.positiveConjugation A ⟨X.val, hX⟩).property

theorem KillingSplit.Construction.KillingSplitWeightData.exists_full_split_invariant_complement (d : KillingSplit.Construction.KillingSplitWeightData B) :
    ∃ U : Submodule ℝ (Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement)),
      IsCompl U (Positive.DerivationInvariantComplement.Construction.positiveDerivationsInWeightRaising B d.basis d.regularElement.val
        (fun i => d.weight i d.regularElement)) ∧
      ∀ A X, X ∈ U → d.ambientPositiveConjugation A X ∈ U := by
  let W := Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement)
  let Φ := (EndomorphismHilbertSchmidt.Construction.continuousEndEuclideanCoordinates d.basis.toBasis).submoduleMap W
  apply TransportedInvariantComplement.Construction.exists_invariant_complement_of_transported_symmetry Φ
    (Positive.DerivationInvariantComplement.Construction.positiveDerivationsInWeightRaising B d.basis d.regularElement.val (fun i => d.weight i d.regularElement))
    (fun A => (d.ambientPositiveConjugation A).toContinuousLinearMap)
  · intro A X Y
    exact d.ambientPositiveConjugation_inner A X Y
  · exact d.positiveDerivationsInWeightRaising_invariant

theorem KillingSplit.Construction.KillingSplitWeightData.regular_flow_eq_ambientPositiveConjugation
    (d : KillingSplit.Construction.KillingSplitWeightData B) (t : ℝ)
    (X : Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement)) :
    Weight.RaisingSplitFlow.Construction.weightRaisingSplitFlow d.basis d.regularElement.val (d.le_symmetric d.regularElement.property).1
      (fun i => d.weight i d.regularElement) (fun i => d.eigenvector i d.regularElement) t X =
      d.ambientPositiveConjugation ((-t) • d.regularElement) X := by
  apply Subtype.ext
  rw [Weight.RaisingSplitFlow.Construction.weightRaisingSplitFlow_val, d.ambientPositiveConjugation_val]
  simp only [SetLike.val_smul, neg_smul, neg_neg]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
