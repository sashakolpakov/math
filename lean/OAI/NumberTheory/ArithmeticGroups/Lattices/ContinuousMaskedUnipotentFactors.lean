import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.RaisingMaskedProduct
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorExponentialUnits

/-! # Continuous Masked Unipotent Factors -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousMaskedUnipotentFactors.Construction

noncomputable section

/-! Continuous complementary exponential factors for every ambient
positive unipotent operator. -/

open NormedSpace

theorem weightRaising_continuous_masked_factors
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (H : L →L[ℝ] L) (hH : H.toLinearMap.IsSymmetric)
    (w : Fin m → ℝ) (heig : ∀ i, H (b i) = w i • b i)
    (r : Fin m → Fin m → Prop) :
    ∃ X Y : UnipotentBracketGroup.Construction.weightRaisingUnitGroup b w → (L →L[ℝ] L), Continuous X ∧ Continuous Y ∧
      ∀ g, X g ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w ∧ Y g ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w ∧
        (∀ i j, ¬r i j → b.repr (X g (b j)) i = 0) ∧
        (∀ i j, r i j → b.repr (Y g (b j)) i = 0) ∧
        g.val = OperatorExponentialUnits.Construction.operatorExpUnit (X g) * OperatorExponentialUnits.Construction.operatorExpUnit (Y g) := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let W := Positive.DerivationNilpotence.Construction.weightRaisingOperators b w
  let P := Weight.RaisingCoordinateMask.Construction.weightRaisingCoordinateMask b w r
  obtain ⟨e, he⟩ := Weight.RaisingMaskedProduct.Construction.weightRaising_masked_exponential_product b H hH w heig r
  let a : W ≃ₜ UnipotentBracketGroup.Construction.weightRaisingUnitGroup b w := NilSubmoduleAffineHomeomorphism.Construction.nilSubmoduleAffineHomeomorph W
    (fun X hX Y hY => Weight.RaisingMultiplication.Construction.weightRaisingOperators_mul b w X Y hX hY)
    (Positive.DerivationNilpotence.Construction.weightRaisingOperators_isNilpotent b w)
  let q : UnipotentBracketGroup.Construction.weightRaisingUnitGroup b w → P.range × P.ker := fun g => e.symm (a.symm g)
  have hq : Continuous q := e.symm.continuous.comp a.symm.continuous
  let X := fun g => (q g).1.val.val
  let Y := fun g => (q g).2.val.val
  have hX : Continuous X := continuous_subtype_val.comp (continuous_subtype_val.comp hq.fst)
  have hY : Continuous Y := continuous_subtype_val.comp (continuous_subtype_val.comp hq.snd)
  refine ⟨X, Y, hX, hY, fun g => ⟨(q g).1.val.property, (q g).2.val.property,
    Weight.RaisingMaskedProduct.Construction.weightRaising_mask_range_support b w r (q g).1.val (q g).1.property,
    Weight.RaisingMaskedProduct.Construction.weightRaising_mask_kernel_support b w r (q g).2.val (q g).2.property, ?_⟩⟩
  have heq := congrArg Subtype.val (e.apply_symm_apply (a.symm g))
  change (e (q g)).val = g.val.val - 1 at heq
  rw [he] at heq
  apply Units.ext
  change g.val.val = exp (X g) * exp (Y g)
  exact (sub_left_inj.mp heq).symm

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ContinuousMaskedUnipotentFactors.Construction
