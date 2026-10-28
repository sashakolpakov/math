import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.DerivationProductCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.InvariantProductCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.NilSubmoduleAffineHomeomorphism
import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentExponentialHomeomorph

/-! # Complementary Unipotent Product -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! The ambient positive unipotent group is a product of a derived
complementary exponential factor and the intrinsic unipotent group. -/

open NormedSpace

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance ComplementaryUnipotentProduct.Construction.complementaryProductEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance ComplementaryUnipotentProduct.Construction.complementaryProductEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance ComplementaryUnipotentProduct.Construction.complementaryProductEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance
local instance ComplementaryUnipotentProduct.Construction.complementaryProduct_complete : CompleteSpace L := FiniteDimensional.complete ℝ L

theorem KillingSplit.Construction.KillingSplitWeightData.exists_complementary_unipotent_product (d : KillingSplit.Construction.KillingSplitWeightData B) :
    ∃ U : Submodule ℝ (Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement)),
      IsCompl U (Positive.DerivationInvariantComplement.Construction.positiveDerivationsInWeightRaising B d.basis d.regularElement.val
        (fun i => d.weight i d.regularElement)) ∧
      (∀ A X, X ∈ U → d.ambientPositiveConjugation A X ∈ U) ∧
      ∃ e : U × UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement) ≃ₜ
        UnipotentBracketGroup.Construction.weightRaisingUnitGroup d.basis (fun i => d.weight i d.regularElement),
        ∀ p, (e p).val = OperatorExponentialUnits.Construction.operatorExpUnit p.1.val.val * p.2.val := by
  let w := fun i => d.weight i d.regularElement
  let W := Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis w
  let V := Positive.DerivationInvariantComplement.Construction.positiveDerivationsInWeightRaising B d.basis d.regularElement.val w
  let : NormedAddCommGroup W := inferInstance
  let : NormedSpace ℝ W := inferInstance
  let : NormedAddCommGroup V := inferInstance
  let : NormedSpace ℝ V := inferInstance
  let : FiniteDimensional ℝ V := inferInstance
  let : NormedAddCommGroup (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) := inferInstance
  let : NormedSpace ℝ (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) := inferInstance
  let : FiniteDimensional ℝ (DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) := inferInstance
  obtain ⟨U, hUV, hU, e, he⟩ := d.exists_split_invariant_product_coordinates
  have hVW : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val ≤ W :=
    Positive.DerivationNilpotence.Construction.positiveBracketDerivations_le_weightRaising B d.basis d.regularElement.val
      (d.le_symmetric d.regularElement.property).1 w (fun i => d.eigenvector i d.regularElement)
  let jlin : V ≃ₗ[ℝ] DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val :=
    Submodule.comapSubtypeEquivOfLe hVW
  let j : V ≃L[ℝ] DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val := jlin.toContinuousLinearEquiv
  let k := d.positiveUnipotentExpHomeomorph.symm.trans j.symm.toHomeomorph
  let u : W ≃ₜ UnipotentBracketGroup.Construction.weightRaisingUnitGroup d.basis w := NilSubmoduleAffineHomeomorphism.Construction.nilSubmoduleAffineHomeomorph W
    (fun X hX Y hY => Weight.RaisingMultiplication.Construction.weightRaisingOperators_mul d.basis w X Y hX hY)
    (Positive.DerivationNilpotence.Construction.weightRaisingOperators_isNilpotent d.basis w)
  let f := (((Homeomorph.refl U).prodCongr k).trans e).trans u
  refine ⟨U, hUV, hU, f, fun p => ?_⟩
  apply Units.ext
  have hy : exp (k p.2).val.val = p.2.val.val := by
    exact congrArg (fun n => n.val.val) (d.positiveUnipotentExpHomeomorph.apply_symm_apply p.2)
  have hv : (f p).val.val = 1 + (e (p.1, k p.2)).val :=
    NilSubmoduleAffineHomeomorphism.Construction.nilSubmoduleAddOne_val W _ _ (e (p.1, k p.2))
  rw [hv, he, hy]
  change 1 + (exp p.1.val.val * p.2.val.val - 1) = exp p.1.val.val * p.2.val.val
  abel

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
