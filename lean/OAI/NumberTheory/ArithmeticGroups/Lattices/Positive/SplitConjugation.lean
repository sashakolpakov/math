import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.DerivationTrace
import OAI.NumberTheory.ArithmeticGroups.Lattices.AdjointExponentialConjugation
import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentExponentialHomeomorph

/-! # Split Conjugation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

section

/-! The linear exponential of the split action represents conjugation
on positive derivations and on their unipotent exponentials. -/

open NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance Positive.SplitConjugation.Construction.splitConjugation_complete : CompleteSpace L := FiniteDimensional.complete ℝ L
local instance Positive.SplitConjugation.Construction.splitConjugationEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance Positive.SplitConjugation.Construction.splitConjugationEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance Positive.SplitConjugation.Construction.splitConjugationEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance
local instance Positive.SplitConjugation.Construction.splitConjugationSub_normed (d : KillingSplit.Construction.KillingSplitWeightData B) :
    NormedAddCommGroup (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) := inferInstance
local instance Positive.SplitConjugation.Construction.splitConjugationSub_space (d : KillingSplit.Construction.KillingSplitWeightData B) :
    NormedSpace ℝ (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) := inferInstance
local instance Positive.SplitConjugation.Construction.splitConjugationSub_finite (d : KillingSplit.Construction.KillingSplitWeightData B) :
    FiniteDimensional ℝ (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) := inferInstance

def KillingSplit.Construction.KillingSplitWeightData.positiveConjugation (d : KillingSplit.Construction.KillingSplitWeightData B) (A : d.subspace) :
    DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val ≃L[ℝ]
      DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val :=
  Bracket.ExponentialEquiv.Construction.continuousLinearMapExpEquiv (d.positiveAction A).toContinuousLinearMap

theorem KillingSplit.Construction.KillingSplitWeightData.positiveConjugation_val (d : KillingSplit.Construction.KillingSplitWeightData B)
    (A : d.subspace) (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    (d.positiveConjugation A X).val = exp A.val * X.val * exp (-A.val) := by
  exact AdjointExponentialConjugation.Construction.exp_represented_commutator (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val).subtypeL
    (d.positiveAction A).toContinuousLinearMap A.val (fun _ => rfl) X

theorem KillingSplit.Construction.KillingSplitWeightData.positiveConjugation_det (d : KillingSplit.Construction.KillingSplitWeightData B)
    (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (A : d.subspace) :
    (d.positiveConjugation A).toLinearEquiv.toLinearMap.det = Real.exp (d.positiveTrace A) :=
  d.positiveAction_exp_det hB hK A

theorem KillingSplit.Construction.KillingSplitWeightData.positiveConjugation_exp_val (d : KillingSplit.Construction.KillingSplitWeightData B)
    (A : d.subspace) (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    exp (d.positiveConjugation A X).val = exp A.val * exp X.val * exp (-A.val) := by
  rw [d.positiveConjugation_val, Split.ConjugationBracketOperators.Construction.exponential_conjugation_exp]

end

/-! Split conjugation of the unipotent subgroup is linear in its
global exponential coordinates. -/

open NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

def KillingSplit.Construction.KillingSplitWeightData.unipotentConjugation (d : KillingSplit.Construction.KillingSplitWeightData B) (A : d.subspace) :
    UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement) ≃ₜ
      UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement) :=
  d.positiveUnipotentExpHomeomorph.symm.trans
    ((d.positiveConjugation A).toHomeomorph.trans d.positiveUnipotentExpHomeomorph)

theorem KillingSplit.Construction.KillingSplitWeightData.unipotentConjugation_exp (d : KillingSplit.Construction.KillingSplitWeightData B)
    (A : d.subspace) (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    d.unipotentConjugation A (d.positiveUnipotentExpHomeomorph X) =
      d.positiveUnipotentExpHomeomorph (d.positiveConjugation A X) := by
  change d.positiveUnipotentExpHomeomorph
    (d.positiveConjugation A (d.positiveUnipotentExpHomeomorph.symm
      (d.positiveUnipotentExpHomeomorph X))) = _
  rw [d.positiveUnipotentExpHomeomorph.symm_apply_apply]

theorem KillingSplit.Construction.KillingSplitWeightData.unipotentConjugation_val (d : KillingSplit.Construction.KillingSplitWeightData B)
    (A : d.subspace)
    (g : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)) :
    (d.unipotentConjugation A g).val.val = exp A.val * g.val.val * exp (-A.val) := by
  obtain ⟨X, rfl⟩ := d.positiveUnipotentExpHomeomorph.surjective g
  rw [d.unipotentConjugation_exp]
  exact d.positiveConjugation_exp_val A X

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
