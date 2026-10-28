import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentLogLocalContinuity
import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ConjugationBracketOperators

/-! # Unipotent Split Flow -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! The contracting split flow acts continuously on positive
derivations and on the unipotent group, intertwining their exponential bijection. -/

open scoped _root_.Topology
open Filter NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance Positive.UnipotentSplitFlow.Construction.splitFlowEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance Positive.UnipotentSplitFlow.Construction.splitFlowEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance Positive.UnipotentSplitFlow.Construction.splitFlowEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance
local instance Positive.UnipotentSplitFlow.Construction.splitFlow_complete : CompleteSpace L := FiniteDimensional.complete ℝ L

def KillingSplit.Construction.KillingSplitWeightData.positiveSplitFlow (d : KillingSplit.Construction.KillingSplitWeightData B) (t : ℝ) :
    DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val →L[ℝ]
      DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val :=
  (((Bracket.ExponentialEquiv.Construction.continuousLinearMapExpEquiv ((-t) • d.regularElement.val)).conjContinuousAlgEquiv.toAlgEquiv.toLinearMap).restrict
    (fun X hX => by
      change exp ((-t) • d.regularElement.val) * X * exp (-((-t) • d.regularElement.val)) ∈ _
      simpa only [neg_smul, neg_neg] using Split.ConjugationBracketOperators.Construction.split_conjugation_preserves_positive_derivations B d.basis
        d.regularElement.val (d.le_symmetric d.regularElement.property)
        (fun i => d.weight i d.regularElement) (fun i => d.eigenvector i d.regularElement) t X hX)).toContinuousLinearMap

theorem KillingSplit.Construction.KillingSplitWeightData.positiveSplitFlow_val
    (d : KillingSplit.Construction.KillingSplitWeightData B) (t : ℝ) (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    (d.positiveSplitFlow t X).val =
      exp ((-t) • d.regularElement.val) * X.val * exp (t • d.regularElement.val) := by
  change exp ((-t) • d.regularElement.val) * X.val * exp (-((-t) • d.regularElement.val)) = _
  simp only [neg_smul, neg_neg]

theorem KillingSplit.Construction.KillingSplitWeightData.positiveSplitFlow_inverse
    (d : KillingSplit.Construction.KillingSplitWeightData B) (t : ℝ) (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    d.positiveSplitFlow (-t) (d.positiveSplitFlow t X) = X := by
  apply Subtype.ext
  rw [d.positiveSplitFlow_val, d.positiveSplitFlow_val]
  exact Split.ConjugationBracketOperators.Construction.split_conjugation_inverse d.regularElement.val X.val t

def KillingSplit.Construction.KillingSplitWeightData.unipotentSplitFlow (d : KillingSplit.Construction.KillingSplitWeightData B) (t : ℝ) :
    UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement) →
      UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement) := fun g =>
  ⟨OperatorExponentialUnits.Construction.operatorExpUnit ((-t) • d.regularElement.val) * g.val * OperatorExponentialUnits.Construction.operatorExpUnit (t • d.regularElement.val), by
    constructor
    · exact Split.ConjugationBracketOperators.Construction.split_conjugation_preserves_bracket B d.regularElement.val
        (d.le_symmetric d.regularElement.property).2 t g.val.val g.property.1
    · change exp ((-t) • d.regularElement.val) * g.val.val * exp (t • d.regularElement.val) - 1 ∈
        Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement)
      rw [Split.ConjugationBracketOperators.Construction.split_conjugation_sub_one]
      exact Weight.ConjugationContraction.Construction.split_conjugation_preserves_weightRaising d.basis d.regularElement.val
        (d.le_symmetric d.regularElement.property).1 (fun i => d.weight i d.regularElement)
        (fun i => d.eigenvector i d.regularElement) t (g.val.val - 1) g.property.2⟩

theorem KillingSplit.Construction.KillingSplitWeightData.unipotentSplitFlow_continuous
    (d : KillingSplit.Construction.KillingSplitWeightData B) (t : ℝ) : Continuous (d.unipotentSplitFlow t) :=
  ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

theorem KillingSplit.Construction.KillingSplitWeightData.positiveUnipotentExp_splitFlow
    (d : KillingSplit.Construction.KillingSplitWeightData B) (t : ℝ) (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    d.positiveUnipotentExp (d.positiveSplitFlow t X) = d.unipotentSplitFlow t (d.positiveUnipotentExp X) := by
  apply Subtype.ext
  apply Units.ext
  change exp (d.positiveSplitFlow t X).val =
    exp ((-t) • d.regularElement.val) * exp X.val * exp (t • d.regularElement.val)
  rw [d.positiveSplitFlow_val]
  simpa only [neg_smul, neg_neg] using Split.ConjugationBracketOperators.Construction.exponential_conjugation_exp ((-t) • d.regularElement.val) X.val

theorem KillingSplit.Construction.KillingSplitWeightData.positiveSplitFlow_contracts
    (d : KillingSplit.Construction.KillingSplitWeightData B) (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    Tendsto (fun t : ℝ => d.positiveSplitFlow t X) atTop (𝓝 0) := by
  apply Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr
  change Tendsto (fun t : ℝ => (d.positiveSplitFlow t X).val) atTop (𝓝 0)
  simp_rw [d.positiveSplitFlow_val]
  apply Weight.ConjugationContraction.Construction.split_conjugation_contracts_weightRaising d.basis d.regularElement.val
    (d.le_symmetric d.regularElement.property).1 (fun i => d.weight i d.regularElement)
    (fun i => d.eigenvector i d.regularElement) X.val
  exact Positive.DerivationNilpotence.Construction.positiveBracketDerivations_le_weightRaising B d.basis d.regularElement.val
    (d.le_symmetric d.regularElement.property).1 (fun i => d.weight i d.regularElement)
    (fun i => d.eigenvector i d.regularElement) X.property

theorem KillingSplit.Construction.KillingSplitWeightData.unipotentSplitFlow_contracts
    (d : KillingSplit.Construction.KillingSplitWeightData B)
    (g : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)) :
    Tendsto (fun t : ℝ => d.unipotentSplitFlow t g) atTop (𝓝 1) := by
  obtain ⟨X, rfl⟩ := d.positiveUnipotentExp_bijective.surjective g
  have h := (d.positiveUnipotentExp_continuous.tendsto 0).comp (d.positiveSplitFlow_contracts X)
  have hz : d.positiveUnipotentExp 0 = 1 := d.positiveUnipotentExpEquiv_zero
  change Tendsto (fun t : ℝ => d.positiveUnipotentExp (d.positiveSplitFlow t X)) atTop
    (𝓝 (d.positiveUnipotentExp 0)) at h
  rw [hz] at h
  simpa only [d.positiveUnipotentExp_splitFlow] using h

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
