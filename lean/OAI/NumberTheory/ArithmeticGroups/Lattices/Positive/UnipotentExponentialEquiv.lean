import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentGlobalExponential
import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingExponentialInjective
import OAI.NumberTheory.ArithmeticGroups.Lattices.KillingSplit
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorExponentialUnits

/-! # Unipotent Exponential Equiv -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Exponentiation is a continuous bijection from the positive
derivations onto the full unipotent bracket subgroup. -/

open NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance Positive.UnipotentExponentialEquiv.Construction.positiveExp_complete : CompleteSpace L := FiniteDimensional.complete ℝ L

def KillingSplit.Construction.KillingSplitWeightData.positiveUnipotentExp (d : KillingSplit.Construction.KillingSplitWeightData B) :
    DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val →
      UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement) := fun X =>
  ⟨OperatorExponentialUnits.Construction.operatorExpUnit X.val, Weight.RaisingExponential.Construction.positive_derivation_exp_mem_unipotent B d.basis d.regularElement.val
    (d.le_symmetric d.regularElement.property).1 (fun i => d.weight i d.regularElement)
    (fun i => d.eigenvector i d.regularElement) X.val X.property⟩

theorem KillingSplit.Construction.KillingSplitWeightData.positiveUnipotentExp_val
    (d : KillingSplit.Construction.KillingSplitWeightData B) (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    ((d.positiveUnipotentExp X).val : L →L[ℝ] L) = exp X.val := rfl

theorem KillingSplit.Construction.KillingSplitWeightData.positiveUnipotentExp_bijective
    (d : KillingSplit.Construction.KillingSplitWeightData B) : Function.Bijective d.positiveUnipotentExp := by
  constructor
  · intro X Y hXY
    apply Subtype.ext
    apply Weight.RaisingExponentialInjective.Construction.exponential_injective_on_weightRaising d.basis d.regularElement.val
      (d.le_symmetric d.regularElement.property).1 (fun i => d.weight i d.regularElement)
      (fun i => d.eigenvector i d.regularElement)
    · exact Positive.DerivationNilpotence.Construction.positiveBracketDerivations_le_weightRaising B d.basis d.regularElement.val
        (d.le_symmetric d.regularElement.property).1 (fun i => d.weight i d.regularElement)
        (fun i => d.eigenvector i d.regularElement) X.property
    · exact Positive.DerivationNilpotence.Construction.positiveBracketDerivations_le_weightRaising B d.basis d.regularElement.val
        (d.le_symmetric d.regularElement.property).1 (fun i => d.weight i d.regularElement)
        (fun i => d.eigenvector i d.regularElement) Y.property
    · exact congrArg (fun g => (g.val : L →L[ℝ] L)) hXY
  · intro g
    obtain ⟨X, hX, he⟩ := UnipotentGlobalExponential.Construction.bracket_unipotent_is_positive_exponential B d.basis d.regularElement.val
      (d.le_symmetric d.regularElement.property) (fun i => d.weight i d.regularElement)
      (fun i => d.eigenvector i d.regularElement) g.val.val g.property.1 g.property.2
    refine ⟨⟨X, hX⟩, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact he

theorem KillingSplit.Construction.KillingSplitWeightData.positiveUnipotentExp_continuous
    (d : KillingSplit.Construction.KillingSplitWeightData B) : Continuous d.positiveUnipotentExp :=
  (OperatorExponentialUnits.Construction.operatorExpUnit_continuous.comp continuous_subtype_val).subtype_mk _

def KillingSplit.Construction.KillingSplitWeightData.positiveUnipotentExpEquiv (d : KillingSplit.Construction.KillingSplitWeightData B) :
    DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val ≃
      UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement) :=
  Equiv.ofBijective d.positiveUnipotentExp d.positiveUnipotentExp_bijective

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
