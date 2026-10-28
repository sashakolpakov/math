import OAI.NumberTheory.ArithmeticGroups.Lattices.RegularWeightOrderRefinement
import OAI.NumberTheory.ArithmeticGroups.Lattices.RegularSplitCentralizer

/-! # Regular Weight Orderings -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Finitely many regular eigenbasis orderings cover every split
diagonal, including points on chamber walls. -/

open scoped Classical

theorem Finite.RegularWeightOrderings.Construction.finite_regular_weight_orderings
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} (w : Fin n → E →ₗ[ℝ] ℝ) :
    ∃ F : Set (Equiv.Perm (Fin n) × E), F.Finite ∧
      (∀ q ∈ F, (∀ i, w i q.2 = 0 ↔ w i = 0) ∧
        (∀ i j, w i q.2 = w j q.2 ↔ w i = w j) ∧ Antitone (fun i => w (q.1 i) q.2)) ∧
      ∀ A : E, ∃ q ∈ F, Monotone (fun i => w (q.1 i) A) := by
  let S : Set (Equiv.Perm (Fin n)) := {σ | ∃ H : E, (∀ i, w i H = 0 ↔ w i = 0) ∧
    (∀ i j, w i H = w j H ↔ w i = w j) ∧ Antitone (fun i => w (σ i) H)}
  have hS : S.Finite := Set.toFinite S
  have hchoose : ∀ σ : S, ∃ H : E, (∀ i, w i H = 0 ↔ w i = 0) ∧
      (∀ i j, w i H = w j H ↔ w i = w j) ∧ Antitone (fun i => w (σ.val i) H) := fun σ => σ.property
  choose H hH using hchoose
  let f : S → Equiv.Perm (Fin n) × E := fun σ => (σ.val, H σ)
  let : Finite S := hS
  refine ⟨Set.range f, Set.finite_range f, ?_, ?_⟩
  · rintro _ ⟨σ, rfl⟩
    exact hH σ
  · intro A
    obtain ⟨σ, K, hK, hsep, hOrder, hA⟩ := RegularWeightOrderRefinement.Construction.exists_regular_weight_permutation w A
    have hs : σ ∈ S := ⟨K, hK, hsep, hOrder⟩
    exact ⟨f ⟨σ, hs⟩, ⟨⟨σ, hs⟩, rfl⟩, hA⟩

def KillingSplit.Construction.KillingSplitWeightData.withRegularElement
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (H : d.subspace) (hH : ∀ i, d.weight i H = 0 ↔ d.weight i = 0) : KillingSplit.Construction.KillingSplitWeightData B where
  subspace := d.subspace
  basis := d.basis
  weight := d.weight
  regularElement := H
  le_symmetric := d.le_symmetric
  commute := d.commute
  eigenvector := d.eigenvector
  regular := hH
  opposite := d.opposite
  centralizer := d.regular_symmetric_centralizer hB hK H hH

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
