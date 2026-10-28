import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.ExponentialDerivative
import OAI.NumberTheory.ArithmeticGroups.Lattices.Bilinear.PreservingCurveTangent
import OAI.NumberTheory.ArithmeticGroups.Lattices.ClosedSubmoduleCurveTangent

/-! # Translated Tangent -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! The left-translated exponential differential preserves the positive
derivation subspace, by differentiating curves in the unipotent group. -/

open NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance Positive.TranslatedTangent.Construction.translatedTangent_complete : CompleteSpace L := FiniteDimensional.complete ℝ L
local instance Positive.TranslatedTangent.Construction.translatedTangentEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance Positive.TranslatedTangent.Construction.translatedTangentEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance Positive.TranslatedTangent.Construction.translatedTangentEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance
local instance Positive.TranslatedTangent.Construction.translatedTangentEnd_rat : NormedAlgebra ℚ (L →L[ℝ] L) :=
  NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)

theorem KillingSplit.Construction.KillingSplitWeightData.positiveLeftDifferentialAmbient_mem
    (d : KillingSplit.Construction.KillingSplitWeightData B) (X Y : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    d.positiveLeftDifferentialAmbient X Y ∈ DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val := by
  let f : ℝ → L →L[ℝ] L := fun t => exp (-X.val) * exp (X + t • Y).val
  have hp : HasDerivAt (fun t : ℝ => X + t • Y) Y 0 := by
    simpa only [one_smul, id_eq] using! ((hasDerivAt_id (0 : ℝ)).smul_const Y).const_add X
  have hd : HasDerivAt f (d.positiveLeftDifferentialAmbient X Y) 0 := by
    have he : HasFDerivAt
        (fun Z : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val => exp (-X.val) * exp Z.val)
        (d.positiveLeftDifferentialAmbient X) (X + (0 : ℝ) • Y) := by
      simpa only [zero_smul, add_zero] using! (d.positive_left_exp_hasStrictFDerivAt X).hasFDerivAt
    exact he.comp_hasDerivAt 0 hp
  have h0 : f 0 = 1 := by
    change exp (-X.val) * exp (X + (0 : ℝ) • Y).val = 1
    simp only [zero_smul, add_zero]
    rw [← exp_add_of_commute (Commute.refl X.val).neg_left, neg_add_cancel, exp_zero]
  have hmem (t : ℝ) :
      (d.positiveUnipotentExp (-X) * d.positiveUnipotentExp (X + t • Y)).val ∈
        UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement) :=
    (d.positiveUnipotentExp (-X) * d.positiveUnipotentExp (X + t • Y)).property
  apply (Positive.DerivationNilpotence.Construction.positiveBracketDerivations_eq_weightRaising B d.basis d.regularElement.val
    (d.le_symmetric d.regularElement.property) (fun i => d.weight i d.regularElement)
    (fun i => d.eigenvector i d.regularElement)).ge
  constructor
  · exact Bilinear.PreservingCurveTangent.Construction.bilinear_preserving_curve_tangent B f _ hd h0 (fun t => (hmem t).1)
  · apply ClosedSubmoduleCurveTangent.Construction.closed_submodule_curve_tangent
      (Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement))
      (Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement)).closed_of_finiteDimensional
      f _ 0 hd
    intro t
    rw [h0]
    exact (hmem t).2

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
