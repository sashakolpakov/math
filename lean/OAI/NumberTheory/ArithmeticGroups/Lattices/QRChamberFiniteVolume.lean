import OAI.NumberTheory.ArithmeticGroups.Lattices.IntrinsicIwasawaQRCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.AdjacentWeightBounds
import OAI.NumberTheory.ArithmeticGroups.Lattices.BoundedUnipotentCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.IntrinsicSiegelFiniteVolume

/-! # QR Chamber Finite Volume -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! General ambient QR chamber cutoffs give finite volume on a
compatible self-adjoint bracket stabilizer. -/

open _root_.ContinuousLinearMap _root_.MeasureTheory _root_.MeasureTheory.Measure

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def QRChamberFiniteVolume.Construction.operatorQRSiegelRegion {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (t c : ℝ) :
    Set (L →L[ℝ] L)ˣ :=
  {g | (∀ i j, i.val + 1 = j.val →
      OperatorQRVal.Construction.operatorQRLogDiagonal b g i - OperatorQRVal.Construction.operatorQRLogDiagonal b g j ≤ t) ∧
    ∀ i j, |OperatorQRVal.Construction.operatorQRUnipotentMatrix b g i j| ≤ c}

variable {B : L →L[ℝ] L →L[ℝ] L}

theorem KillingSplit.Construction.KillingSplitWeightData.qrSiegelIntersection_subset
    (d : KillingSplit.Construction.KillingSplitWeightData B) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hd : Antitone (fun i => d.weight i d.regularElement))
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (hDadj : ∀ X, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint X) = 0)
    (t c : ℝ) (ht : 0 ≤ t) :
    {g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B | g.val ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion d.basis t c} ⊆
      d.intrinsicSiegelSet ((Module.finrank ℝ L : ℝ) * t) (d.boundedUnipotentSet c) := by
  intro g hg
  obtain ⟨k, hk, A, n, hn, he, hdiag, hu⟩ :=
    d.intrinsic_iwasawa_qr_coordinates hd hadj hDadj g.val g.property
  have hA : A ∈ d.truncatedNegativeChamber ((Module.finrank ℝ L : ℝ) * t) := by
    apply d.chamber_of_adjacent_weight_bounds hK hd A t ht
    intro i j hij
    rw [← hdiag i, ← hdiag j]
    exact hg.1 i j hij
  have hnC : (⟨n, hn⟩ : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis
      (fun i => d.weight i d.regularElement)) ∈ d.boundedUnipotentSet c := by
    intro i j
    rw [← hu]
    exact hg.2 i j
  exact d.mem_intrinsicSiegelSet_of_factors _ _ g ⟨k, hk⟩ A hA ⟨n, hn⟩ hnC he

theorem KillingSplit.Construction.KillingSplitWeightData.qrSiegelIntersection_inverseHaar_lt_top
    [MeasurableSpace (L →L[ℝ] L)ˣ] [BorelSpace (L →L[ℝ] L)ˣ]
    (d : KillingSplit.Construction.KillingSplitWeightData B) (hB : ContinuousBracketConstraints.Construction.IsContinuousLieBracket B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hd : Antitone (fun i => d.weight i d.regularElement))
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (hDadj : ∀ X, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint X) = 0)
    (μ : Measure (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)) [IsHaarMeasure μ]
    (t c : ℝ) (ht : 0 ≤ t) :
    μ.inv {g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B | g.val ∈ QRChamberFiniteVolume.Construction.operatorQRSiegelRegion d.basis t c} < ⊤ := by
  apply (measure_mono (d.qrSiegelIntersection_subset hK hd hadj hDadj t c ht)).trans_lt
  exact d.intrinsicSiegelSet_inverseHaar_lt_top hB hK hadj hDadj μ _
    (mul_nonneg (Nat.cast_nonneg _) ht) _ (d.boundedUnipotentSet_isCompact hd c)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
