import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.InvariantComplement
import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingProductCoordinates

/-! # Invariant Product Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! A complement invariant under the full split group gives global
product coordinates with the intrinsic positive derivations. -/

open NormedSpace

theorem KillingSplit.Construction.KillingSplitWeightData.exists_split_invariant_product_coordinates
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B) :
    ∃ U : Submodule ℝ (Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement)),
      IsCompl U (Positive.DerivationInvariantComplement.Construction.positiveDerivationsInWeightRaising B d.basis d.regularElement.val
        (fun i => d.weight i d.regularElement)) ∧
      (∀ A X, X ∈ U → d.ambientPositiveConjugation A X ∈ U) ∧
      ∃ e : U × Positive.DerivationInvariantComplement.Construction.positiveDerivationsInWeightRaising B d.basis d.regularElement.val
          (fun i => d.weight i d.regularElement) ≃ₜ
          Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement),
        ∀ p, (e p).val = exp p.1.val.val * exp p.2.val.val - 1 := by
  obtain ⟨U, hUV, hU⟩ := d.exists_full_split_invariant_complement
  have hUr : ∀ t X, X ∈ U → Weight.RaisingSplitFlow.Construction.weightRaisingSplitFlow d.basis d.regularElement.val
      (d.le_symmetric d.regularElement.property).1 (fun i => d.weight i d.regularElement)
      (fun i => d.eigenvector i d.regularElement) t X ∈ U := by
    intro t X hX
    rw [d.regular_flow_eq_ambientPositiveConjugation]
    exact hU _ X hX
  obtain ⟨e, he⟩ := Weight.RaisingProductCoordinates.Construction.weightRaising_exists_exponential_product_homeomorph d.basis d.regularElement.val
    (d.le_symmetric d.regularElement.property).1 (fun i => d.weight i d.regularElement)
    (fun i => d.eigenvector i d.regularElement) U _ hUV hUr
    (Positive.DerivationInvariantComplement.Construction.positiveDerivationsInWeightRaising_split_invariant B d.basis d.regularElement.val
      (d.le_symmetric d.regularElement.property) (fun i => d.weight i d.regularElement)
      (fun i => d.eigenvector i d.regularElement))
  exact ⟨U, hUV, hU, e, he⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
