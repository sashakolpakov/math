import OAI.ArithmeticGeometry.Descent.CMVariety.Rigidity
import OAI.AlgebraicGeometry.ComplexMultiplication.DecompositionEmbeddingBasis

/-! # Split Periods -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.SplitPeriods.Abelian

noncomputable section

/-!
Finiteness of periods after retaining the full rational splitting and the
CM-field action on each rank-one summand. The rational subspaces, fields,
and scalar actions are fixed; only their Hodge structures vary.
-/

open OAI.AlgebraicGeometry.ComplexMultiplication.DecompositionEmbeddingBasis.CM

variable {U : Type*} [AddCommGroup U] [Module ℚ U]
  {H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U} (D : AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition H)

/-- A period compatible with the fixed rational splitting and the fixed
CM-field actions. No discreteness or algebraicity is included as data. -/
structure SplitCMPeriod where
  hodge : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U
  componentPeriod : ∀ i : Fin D.numberOfComponents,
    Rigidity.Abelian.RankOneCMPeriod (D.component i).field (D.component i).subspace
  inclusion_hodge : ∀ i, AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.IsHodgeMap (componentPeriod i).val hodge
    (D.component i).subspace.subtype

namespace SplitCMPeriod

/-- Recover the CM decomposition using the new Hodge subspaces while
keeping all rational subspaces and CM-field actions fixed. -/
def decomposition (P : SplitCMPeriod D) : AlgebraicGeometry.ComplexMultiplication.Decomposition.CM.CMDecomposition P.hodge where
  numberOfComponents := D.numberOfComponents
  component i := {
    subspace := (D.component i).subspace
    hodge := (P.componentPeriod i).val
    inclusion_hodge := P.inclusion_hodge i
    field := (D.component i).field
    fieldStructure := (D.component i).fieldStructure
    fieldAlgebra := (D.component i).fieldAlgebra
    scalarAction := (D.component i).scalarAction
    scalarTower := (D.component i).scalarTower
    cm := (P.componentPeriod i).property }
  isInternal := D.isInternal

/-- The holomorphic types of the summands determine the ambient type. -/
theorem holomorphic_le_of_component_eq (P Q : SplitCMPeriod D)
    (hPQ : P.componentPeriod = Q.componentPeriod) :
    P.hodge.holomorphic ≤ Q.hodge.holomorphic := by
  let DP := P.decomposition D
  have hspan : P.hodge.holomorphic =
      Submodule.span ℂ (DP.embeddingBasis '' {j | DP.embeddingSign j = true}) :=
    DP.signSubspace_eq_span_embeddingBasis true
  rw [hspan]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨i, σ⟩, hσ, rfl⟩
  have : NumberField (DP.component i).field := (DP.component i).cm.numberField
  rw [DP.embeddingBasis_apply]
  apply Q.inclusion_hodge i
  have hi : (P.componentPeriod i).val.holomorphic =
      (Q.componentPeriod i).val.holomorphic :=
    congrArg (fun C => C.val.holomorphic) (congrFun hPQ i)
  rw [← hi]
  exact ((DP.component i).cm.embeddingBasis_mem_holomorphic_iff σ).mpr hσ

/-- Forgetting the ambient Hodge structure loses no information. -/
theorem componentPeriod_injective :
    Function.Injective (fun P : SplitCMPeriod D => P.componentPeriod) := by
  intro P Q hPQ
  have hh : P.hodge = Q.hodge := Rigidity.Abelian.weightOne_eq_of_holomorphic_eq P.hodge Q.hodge
    (le_antisymm (holomorphic_le_of_component_eq D P Q hPQ)
      (holomorphic_le_of_component_eq D Q P hPQ.symm))
  rcases P with ⟨hP, cP, iP⟩
  rcases Q with ⟨hQ, cQ, iQ⟩
  dsimp only at hPQ hh
  cases hh
  cases hPQ
  rfl

end SplitCMPeriod

/-- A fixed finite direct sum of rank-one CM representations has only
finitely many compatible enhanced Hodge periods. -/
theorem split_CM_periods_finite : Finite (SplitCMPeriod D) := by
  have (i : Fin D.numberOfComponents) : NumberField (D.component i).field :=
    (D.component i).cm.numberField
  have (i : Fin D.numberOfComponents) :
      Finite (Rigidity.Abelian.RankOneCMPeriod (D.component i).field (D.component i).subspace) :=
    Rigidity.Abelian.rankOne_CM_periods_finite
  exact Finite.of_injective _ (SplitCMPeriod.componentPeriod_injective D)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.SplitPeriods.Abelian
