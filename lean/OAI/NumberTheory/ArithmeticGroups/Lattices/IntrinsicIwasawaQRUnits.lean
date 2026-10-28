import OAI.NumberTheory.ArithmeticGroups.Lattices.IntrinsicIwasawaQRCoordinates
import OAI.NumberTheory.ArithmeticGroups.Lattices.Ambient.UpperSplitConjugation
import OAI.NumberTheory.ArithmeticGroups.Lattices.QRPositiveUnit

/-! # Intrinsic Iwasawa QR Units -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! The intrinsic Iwasawa split and unipotent factors are the
ambient positive diagonal and unipotent QR matrix units. -/

open _root_.ContinuousLinearMap

theorem KillingSplit.Construction.KillingSplitWeightData.intrinsic_iwasawa_qr_units
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B)
    (hd : Antitone (fun i => d.weight i d.regularElement))
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (hDadj : ∀ X, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint X) = 0)
    (g : (L →L[ℝ] L)ˣ) (hg : g ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) :
    ∃ k : OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B, ∃ A : d.subspace,
      ∃ n : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement),
        g = k.val * OperatorExponentialUnits.Construction.operatorExpUnit A.val * n.val ∧
        QRPositiveUnit.Construction.operatorQRPositiveDiagonalUnit d.basis g = d.ambientSplitMatrixUnit A ∧
        OperatorQRVal.Construction.operatorQRUnipotentUnit d.basis g = ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv d.basis.toBasis n.val := by
  obtain ⟨k, hk, A, n, hn, he, hlog, hu⟩ := d.intrinsic_iwasawa_qr_coordinates hd hadj hDadj g hg
  refine ⟨⟨k, hk⟩, A, ⟨n, hn⟩, he, ?_, ?_⟩
  · apply Units.ext
    change Matrix.diagonal (fun i => Real.exp (OperatorQRVal.Construction.operatorQRLogDiagonal d.basis g i)) =
      (d.ambientSplitMatrixUnit A).val
    rw [d.ambientSplitMatrixUnit_val]
    congr 1
    funext i
    rw [hlog i]
  · apply Units.ext
    rw [OperatorQRVal.Construction.operatorQRUnipotentUnit_val]
    exact hu

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
