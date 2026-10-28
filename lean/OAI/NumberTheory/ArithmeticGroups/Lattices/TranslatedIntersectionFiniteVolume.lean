import OAI.NumberTheory.ArithmeticGroups.Lattices.NormalizedIntersectionFiniteVolume
import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalSiegelBruhatReduction

/-! # Translated Intersection Finite Volume -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

section

/-! Every fixed translated ambient Siegel region has finite
intersection volume in a self-adjoint bracket stabilizer. -/

open _root_.ContinuousLinearMap _root_.MeasureTheory _root_.MeasureTheory.Measure

theorem KillingSplit.Construction.KillingSplitWeightData.translated_intersection_inverseHaar_lt_top
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    [MeasurableSpace (L →L[ℝ] L)ˣ] [BorelSpace (L →L[ℝ] L)ˣ]
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hd : Antitone (fun i => d.weight i d.regularElement))
    (hsep : ∀ i j, d.weight i d.regularElement = d.weight j d.regularElement → d.weight i = d.weight j)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (hDadj : ∀ X, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint X) = 0)
    (μ : Measure (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)) [IsHaarMeasure μ]
    (M : (Matrix (Fin (Module.finrank ℝ L)) (Fin (Module.finrank ℝ L)) ℝ)ˣ)
    (C : Set (UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup (Module.finrank ℝ L))) (hC : IsCompact C)
    (t : ℝ) (ht : 0 ≤ t) :
    μ.inv {g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B | g.val ∈ OrthogonalSiegelBruhatReduction.Construction.orthogonalTranslatedSiegelSet d.basis M t C} < ⊤ := by
  let F := ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis
  obtain ⟨p⟩ := d.ambientUnipotentProductData_nonempty hd
  obtain ⟨V, σ, C', t', hC', ht', hReduction⟩ := OrthogonalSiegelBruhatReduction.Construction.orthogonalTranslatedSiegelSet_bruhat_reduction d.basis M C hC t ht
  obtain ⟨v, hv, hV⟩ := p.split_off_intrinsic_factor V
  let γ := p.intrinsicProjection V
  let γH : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B := ⟨γ.val, γ.property.1⟩
  let T : Set (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) :=
    {g | g.val ∈ OrthogonalSiegelBruhatReduction.Construction.orthogonalTranslatedSiegelSet d.basis (PermutationMatrixUnits.Construction.permutationMatrixUnit σ * v.val) t' C'}
  have hT : μ.inv T < ⊤ := d.normalized_intersection_inverseHaar_lt_top hB hK hd p hsep hadj hDadj μ C' hC' t' ht' σ v hv
  have hVmat : V.val = v.val * F γ.val := congrArg Subtype.val hV
  have hsub : {g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B | g.val ∈ OrthogonalSiegelBruhatReduction.Construction.orthogonalTranslatedSiegelSet d.basis M t C} ⊆
      (fun g => g * γH⁻¹) ⁻¹' T := by
    intro g hg
    have hR := hReduction hg
    rw [hVmat, ← mul_assoc] at hR
    have hRemove := OrthogonalSiegelBruhatReduction.Construction.orthogonalTranslatedSiegelSet_remove_right_factor d.basis
      (PermutationMatrixUnits.Construction.permutationMatrixUnit σ * v.val) C' t' γ.val g.val hR
    exact hRemove
  apply (measure_mono hsub).trans_lt
  rw [measure_preimage_mul_right]
  exact hT

end

/-! Finite translated-intersection volume in the continuous QR
region formulation used by ambient lattice reduction. -/

open _root_.ContinuousLinearMap _root_.MeasureTheory _root_.MeasureTheory.Measure

theorem KillingSplit.Construction.KillingSplitWeightData.qr_translated_intersection_inverseHaar_lt_top
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    [MeasurableSpace (L →L[ℝ] L)ˣ] [BorelSpace (L →L[ℝ] L)ˣ]
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hd : Antitone (fun i => d.weight i d.regularElement))
    (hsep : ∀ i j, d.weight i d.regularElement = d.weight j d.regularElement → d.weight i = d.weight j)
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (hDadj : ∀ X, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint X) = 0)
    (μ : Measure (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)) [IsHaarMeasure μ]
    (x : (L →L[ℝ] L)ˣ) (t c : ℝ) (ht : 0 ≤ t) :
    μ.inv {g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B | ∃ u ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion d.basis t c, g.val = u * x} < ⊤ := by
  have hsub : {g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B | ∃ u ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion d.basis t c, g.val = u * x} ⊆
      {g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B | g.val ∈ OrthogonalSiegelBruhatReduction.Construction.orthogonalTranslatedSiegelSet d.basis
        (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis x) t (BoundedUpperUnipotentSet.Construction.boundedUpperUnipotentSet (Module.finrank ℝ L) c)} := by
    rintro g ⟨u, hu, he⟩
    change g.val ∈ OrthogonalSiegelBruhatReduction.Construction.orthogonalTranslatedSiegelSet d.basis
      (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis x) t (BoundedUpperUnipotentSet.Construction.boundedUpperUnipotentSet _ c)
    rw [he]
    exact OrthogonalSiegelBruhatReduction.Construction.orthogonalTranslatedSiegelSet_of_qr_right_translate d.basis x u t c hu
  apply (measure_mono hsub).trans_lt
  exact d.translated_intersection_inverseHaar_lt_top hB hK hd hsep hadj hDadj μ _ _
    (BoundedUpperUnipotentSet.Construction.boundedUpperUnipotentSet_isCompact (Module.finrank ℝ L) c) t ht

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
