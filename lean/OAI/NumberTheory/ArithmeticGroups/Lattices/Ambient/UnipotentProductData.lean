import OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.UnipotentTripleProduct
import OAI.NumberTheory.ArithmeticGroups.Lattices.ZeroWeightBlockCentralizer
import OAI.NumberTheory.ArithmeticGroups.Lattices.Positive.SplitConjugation

/-! # Unipotent Product Data -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! A bundled three-factor decomposition of the ambient upper
unipotent group, obtained from the proved complementary product theorem. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

structure Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData (d : KillingSplit.Construction.KillingSplitWeightData B)
    (hd : Antitone (fun i => d.weight i d.regularElement)) where
  complement : Submodule ℝ (Positive.DerivationNilpotence.Construction.weightRaisingOperators d.basis (fun i => d.weight i d.regularElement))
  isCompl : IsCompl complement (Positive.DerivationInvariantComplement.Construction.positiveDerivationsInWeightRaising B d.basis d.regularElement.val
    (fun i => d.weight i d.regularElement))
  invariant : ∀ A X, X ∈ complement → d.ambientPositiveConjugation A X ∈ complement
  product : (UpperUnipotentBlockRetraction.Construction.upperUnitriangularBlockProjection (fun i => d.weight i d.regularElement) hd).range ×
    (complement × UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)) ≃ₜ
    UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L)
  product_val : ∀ p, (product p).val = p.1.val.val *
    ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis (OperatorExponentialUnits.Construction.operatorExpUnit p.2.1.val.val) *
    ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis p.2.2.val

theorem KillingSplit.Construction.KillingSplitWeightData.ambientUnipotentProductData_nonempty
    (d : KillingSplit.Construction.KillingSplitWeightData B) (hd : Antitone (fun i => d.weight i d.regularElement)) :
    Nonempty (Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData d hd) := by
  obtain ⟨U, hU, hInv, e, he⟩ := d.exists_ambient_unipotent_triple_product hd
  exact ⟨⟨U, hU, hInv, e, he⟩⟩

def Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData.intrinsicProjection {d : KillingSplit.Construction.KillingSplitWeightData B}
    {hd : Antitone (fun i => d.weight i d.regularElement)} (p : Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData d hd) :
    UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L) →
      UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement) :=
  fun n => (p.product.symm n).2.2

theorem Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData.intrinsicProjection_continuous {d : KillingSplit.Construction.KillingSplitWeightData B}
    {hd : Antitone (fun i => d.weight i d.regularElement)} (p : Ambient.UnipotentProductData.Construction.AmbientUnipotentProductData d hd) :
    Continuous p.intrinsicProjection := p.product.symm.continuous.snd.snd

def KillingSplit.Construction.KillingSplitWeightData.intrinsicUpperInclusion (d : KillingSplit.Construction.KillingSplitWeightData B)
    (hd : Antitone (fun i => d.weight i d.regularElement)) :
    UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement) →*
      UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L) where
  toFun n := ⟨ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis n.val, d.ordered_unipotent_matrix_upper hd n⟩
  map_one' := by apply Subtype.ext; exact map_one (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis)
  map_mul' n m := by apply Subtype.ext; exact map_mul (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis) n.val m.val

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
