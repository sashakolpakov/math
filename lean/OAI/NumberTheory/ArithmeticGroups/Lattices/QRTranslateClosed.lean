import OAI.NumberTheory.ArithmeticGroups.Lattices.TranslatedIntersectionFiniteVolume
import OAI.NumberTheory.ArithmeticGroups.Lattices.QRRegionBasisCovariance
import OAI.NumberTheory.ArithmeticGroups.Lattices.AutomorphismAdjointDerivations

/-! # QR Translate Closed -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.QRTranslateClosed.Construction

noncomputable section

section

/-! Finite translated QR intersection volume for a self-adjoint
Killing bracket in any orthonormal ambient basis. -/

open _root_.ContinuousLinearMap _root_.MeasureTheory _root_.MeasureTheory.Measure

theorem selfAdjoint_bracket_qr_translated_inverseHaar_lt_top
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    [MeasurableSpace (L →L[ℝ] L)ˣ] [BorelSpace (L →L[ℝ] L)ˣ]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (B : L →L[ℝ] L →L[ℝ] L)
    (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (μ : Measure (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)) [IsHaarMeasure μ]
    (x : (L →L[ℝ] L)ˣ) (t c : ℝ) (ht : 0 ≤ t) :
    μ.inv {g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B | ∃ u ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion b t c, g.val = u * x} < ⊤ := by
  have hm : m = Module.finrank ℝ L := by
    simpa only [Fintype.card_fin] using (Module.finrank_eq_card_basis b.toBasis).symm
  subst m
  obtain ⟨d, hd, hsep⟩ := OrderedSplitWeightData.Construction.exists_ordered_killing_split_weight_data B hB hK
  let p := OperatorQRVal.Construction.orthonormalBasisChangeUnit b d.basis
  have hsub : {g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B | ∃ u ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion b t c, g.val = u * x} ⊆
      {g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B | ∃ u ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion d.basis t c, g.val = u * (p * x)} := by
    rintro g ⟨u, hu, he⟩
    refine ⟨u * p⁻¹, (QRRegionBasisCovariance.Construction.operatorQRSiegelRegion_basis_covariance b d.basis u t c).mpr hu, ?_⟩
    rw [he]
    group
  apply (measure_mono hsub).trans_lt
  exact d.qr_translated_intersection_inverseHaar_lt_top hB hK hd (fun i j => (hsep i j).mp)
    hadj (AutomorphismAdjointDerivations.Construction.bracket_derivation_adjoint_of_automorphism_adjoint B hadj) μ (p * x) t c ht

end

/-! Closed QR intersection pieces provide measurable finite-volume
sets for the arithmetic fundamental-domain construction. -/

open _root_.ContinuousLinearMap _root_.MeasureTheory _root_.MeasureTheory.Measure

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem operatorQRSiegelRegion_isClosed {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (t c : ℝ) :
    IsClosed (QRChamberFiniteVolume.Construction.operatorQRSiegelRegion b t c) := by
  have hH (i : Fin m) : Continuous (fun g => OperatorQRVal.Construction.operatorQRLogDiagonal b g i) :=
    (continuous_apply i).comp (OperatorQRVal.Construction.operatorQRLogDiagonal_continuous b)
  have hU (i j : Fin m) : Continuous (fun g => OperatorQRVal.Construction.operatorQRUnipotentMatrix b g i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp (OperatorQRVal.Construction.operatorQRUnipotentMatrix_continuous b))
  have h₁ : IsClosed {g : (L →L[ℝ] L)ˣ | ∀ i j, i.val + 1 = j.val →
      OperatorQRVal.Construction.operatorQRLogDiagonal b g i - OperatorQRVal.Construction.operatorQRLogDiagonal b g j ≤ t} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le ((hH i).sub (hH j)) continuous_const
  have h₂ : IsClosed {g : (L →L[ℝ] L)ˣ | ∀ i j, |OperatorQRVal.Construction.operatorQRUnipotentMatrix b g i j| ≤ c} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_le (hU i j).abs continuous_const
  exact h₁.inter h₂

def qrTranslateIntersection {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (B : L →L[ℝ] L →L[ℝ] L) (x : (L →L[ℝ] L)ˣ) (t c : ℝ) : Set (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) :=
  {g | g.val * x⁻¹ ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion b t c}

theorem qrTranslateIntersection_isClosed {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (B : L →L[ℝ] L →L[ℝ] L) (x : (L →L[ℝ] L)ˣ) (t c : ℝ) :
    IsClosed (qrTranslateIntersection b B x t c) :=
  (operatorQRSiegelRegion_isClosed b t c).preimage (continuous_subtype_val.mul continuous_const)

theorem qrTranslateIntersection_eq {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (B : L →L[ℝ] L →L[ℝ] L) (x : (L →L[ℝ] L)ˣ) (t c : ℝ) :
    qrTranslateIntersection b B x t c =
      {g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B | ∃ u ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion b t c, g.val = u * x} := by
  ext g
  constructor
  · intro hg
    exact ⟨g.val * x⁻¹, hg, by group⟩
  · rintro ⟨u, hu, he⟩
    change g.val * x⁻¹ ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion b t c
    rw [he, mul_assoc, mul_inv_cancel, mul_one]
    exact hu

theorem qrTranslateIntersection_inverseHaar_lt_top
    [MeasurableSpace (L →L[ℝ] L)ˣ] [BorelSpace (L →L[ℝ] L)ˣ]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (B : L →L[ℝ] L →L[ℝ] L)
    (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (μ : Measure (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)) [IsHaarMeasure μ]
    (x : (L →L[ℝ] L)ˣ) (t c : ℝ) (ht : 0 ≤ t) : μ.inv (qrTranslateIntersection b B x t c) < ⊤ := by
  rw [qrTranslateIntersection_eq]
  exact selfAdjoint_bracket_qr_translated_inverseHaar_lt_top b B hB hK hadj μ x t c ht

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.QRTranslateClosed.Construction
