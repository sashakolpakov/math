import OAI.NumberTheory.ArithmeticGroups.Lattices.PositiveBlockKernelEquiv
import OAI.NumberTheory.ArithmeticGroups.Lattices.ComplementaryUnipotentProduct

/-! # Unipotent Triple Product -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! The full upper unipotent group has three-factor coordinates:
equal-weight blocks, a split-invariant complement, and intrinsic unipotents. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

local instance Ambient.UnipotentTripleProduct.Construction.tripleProductEnd_normed : NormedAddCommGroup (L →L[ℝ] L) := inferInstance
local instance Ambient.UnipotentTripleProduct.Construction.tripleProductEnd_space : NormedSpace ℝ (L →L[ℝ] L) := inferInstance
local instance Ambient.UnipotentTripleProduct.Construction.tripleProductEnd_finite : FiniteDimensional ℝ (L →L[ℝ] L) := inferInstance

theorem KillingSplit.Construction.KillingSplitWeightData.exists_ambient_unipotent_triple_product
    (d : KillingSplit.Construction.KillingSplitWeightData B) (hd : Antitone (fun i => d.weight i d.regularElement)) :
    ∃ U : Submodule ℝ (Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement)),
      IsCompl U (Positive.DerivationInvariantComplement.Construction.positiveDerivationsInWeightRaising B d.basis d.regularElement.val
        (fun i => d.weight i d.regularElement)) ∧
      (∀ A X, X ∈ U → d.ambientPositiveConjugation A X ∈ U) ∧
      ∃ e : (UpperUnipotentBlockRetraction.Construction.upperUnitriangularBlockProjection (fun i => d.weight i d.regularElement) hd).range ×
        (U × UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)) ≃ₜ
        UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L),
        ∀ p, (e p).val = p.1.val.val *
          ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis (OperatorExponentialUnits.Construction.operatorExpUnit p.2.1.val.val) *
          ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis p.2.2.val := by
  obtain ⟨U, hUV, hU, f, hf⟩ := d.exists_complementary_unipotent_product
  let w := fun i => d.weight i d.regularElement
  let k := PositiveBlockKernelEquiv.Construction.orderedPositiveBlockKernelEquiv d.basis w hd
  let e := ((Homeomorph.refl (UpperUnipotentBlockRetraction.Construction.upperUnitriangularBlockProjection w hd).range).prodCongr
    (f.trans k.toHomeomorph)).trans (UpperUnipotentBlockRetraction.Construction.upperUnitriangularBlockProductHomeomorph w hd)
  refine ⟨U, hUV, hU, e, fun p => ?_⟩
  change p.1.val.val * ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis (f p.2).val = _
  rw [hf, map_mul, mul_assoc]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
