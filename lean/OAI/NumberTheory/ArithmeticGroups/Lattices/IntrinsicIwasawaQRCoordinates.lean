import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRDiagonalTranslation
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRVal
import OAI.NumberTheory.ArithmeticGroups.Lattices.IntrinsicMatrixKANBounds

/-! # Intrinsic Iwasawa QR Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! In a compatible ordered basis, ambient QR coordinates coincide
with the intrinsic split and unipotent Iwasawa coordinates. -/

open _root_.ContinuousLinearMap

theorem KillingSplit.Construction.KillingSplitWeightData.intrinsic_iwasawa_qr_coordinates
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B)
    (hd : Antitone (fun i => d.weight i d.regularElement))
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (hDadj : ∀ X, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint X) = 0)
    (g : (L →L[ℝ] L)ˣ) (hg : g ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) :
    ∃ k ∈ OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B, ∃ A : d.subspace,
      ∃ n ∈ UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement),
        g = k * OperatorExponentialUnits.Construction.operatorExpUnit A.val * n ∧
        (∀ i, OperatorQRVal.Construction.operatorQRLogDiagonal d.basis g i = d.weight i A) ∧
        OperatorQRVal.Construction.operatorQRUnipotentMatrix d.basis g = ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis n.val := by
  obtain ⟨k, hk, A, n, hn, he⟩ := d.global_iwasawa hadj hDadj g hg
  have hm : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis g.val =
      ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis k.val * Matrix.diagonal (fun i => Real.exp (d.weight i A)) *
        ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis n.val := by
    have hv : g.val = k.val * (OperatorExponentialUnits.Construction.operatorExpUnit A.val).val * n.val := congrArg Units.val he
    rw [hv, map_mul, map_mul]
    rw [show (OperatorExponentialUnits.Construction.operatorExpUnit A.val).val = NormedSpace.exp A.val from rfl, d.exponential_matrix]
  obtain ⟨_, hdiag, hu⟩ := OperatorQRDiagonalTranslation.Construction.operatorQR_kan_unique d.basis g _ _ _
    (OrthogonalOperatorMatrices.Construction.orthogonalBracketUnit_matrix d.basis B k hk) (fun i => Real.exp_pos _)
    (d.ordered_unipotent_matrix_upper hd ⟨n, hn⟩) hm
  refine ⟨k, hk, A, n, hn, he, fun i => ?_, hu⟩
  change Real.log (OperatorQRBasis.Construction.operatorQRDiagonal d.basis g i) = _
  rw [congrFun hdiag i, Real.log_exp]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
