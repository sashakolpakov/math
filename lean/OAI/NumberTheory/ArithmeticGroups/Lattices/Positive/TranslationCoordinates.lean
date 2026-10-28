import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentExponentialHomeomorph

/-! # Translation Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Left translations of the unipotent subgroup in exponential
coordinates form explicit homeomorphisms of the positive derivations. -/

open NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

def KillingSplit.Construction.KillingSplitWeightData.positiveLeftTranslation (d : KillingSplit.Construction.KillingSplitWeightData B)
    (g : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)) :
    DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val ≃ₜ
      DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val :=
  d.positiveUnipotentExpHomeomorph.trans
    ((Homeomorph.mulLeft g).trans d.positiveUnipotentExpHomeomorph.symm)

theorem KillingSplit.Construction.KillingSplitWeightData.positiveLeftTranslation_exp (d : KillingSplit.Construction.KillingSplitWeightData B)
    (g : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))
    (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    d.positiveUnipotentExpHomeomorph (d.positiveLeftTranslation g X) =
      g * d.positiveUnipotentExpHomeomorph X := by
  exact d.positiveUnipotentExpHomeomorph.apply_symm_apply _

theorem KillingSplit.Construction.KillingSplitWeightData.positiveLeftTranslation_exp_val (d : KillingSplit.Construction.KillingSplitWeightData B)
    (g : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement))
    (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    exp (d.positiveLeftTranslation g X).val = g.val.val * exp X.val :=
  congrArg (fun h => h.val.val) (d.positiveLeftTranslation_exp g X)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
