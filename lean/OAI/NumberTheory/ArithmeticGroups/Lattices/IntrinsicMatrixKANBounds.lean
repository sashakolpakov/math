import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixKANUniqueness
import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalOperatorMatrices
import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ExponentialMatrixChamber
import OAI.NumberTheory.ArithmeticGroups.Lattices.OrderedTriangularCompatibility
import OAI.NumberTheory.ArithmeticGroups.Lattices.WeightedGlobalIwasawa

/-! # Intrinsic Matrix KAN Bounds -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! An ambient KAN factorization with bounded unipotent coordinates
gives the same bounds on the intrinsic Iwasawa factors. -/

open _root_.ContinuousLinearMap
open scoped Classical

def IntrinsicMatrixKANBounds.Construction.IsBoundedSiegelMatrix {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (c : ℝ) : Prop :=
  ∃ (K U : Matrix (Fin m) (Fin m) ℝ) (a : Fin m → ℝ),
    K ∈ Matrix.orthogonalGroup (Fin m) ℝ ∧
    (∀ i, 0 < a i) ∧
    (∀ i j, i.val + 1 = j.val → a i ≤ 2 * a j) ∧
    UpperUnitriangularMatrices.Construction.IsUpperUnitriangular U ∧ (∀ i j, |U i j| ≤ c) ∧
    M = K * Matrix.diagonal a * U

theorem KillingSplit.Construction.KillingSplitWeightData.iwasawa_factors_of_matrix_bounds
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B)
    (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hd : Antitone (fun i => d.weight i d.regularElement))
    (hadj : ∀ g : L ≃L[ℝ] L, ContinuousBracketChange.Construction.continuousBracketChange g B = B →
      ∀ x y, adjoint g.toContinuousLinearMap (B x y) =
        B (adjoint g.toContinuousLinearMap x) (adjoint g.toContinuousLinearMap y))
    (hDadj : ∀ X, Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B X = 0 →
      Lie.AutomorphismTransversal.Construction.continuousBilinearDerivationDefect B (adjoint X) = 0)
    (g : (L →L[ℝ] L)ˣ) (hg : g ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) (c : ℝ)
    (hM : IntrinsicMatrixKANBounds.Construction.IsBoundedSiegelMatrix (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis g.val) c) :
    ∃ k ∈ OrthogonalBracketUnitCompactness.Construction.orthogonalBracketUnitGroup B, ∃ A : d.subspace,
      A ∈ d.truncatedNegativeChamber (Real.log ((2 : ℝ) ^ Module.finrank ℝ L)) ∧
      ∃ n ∈ UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement),
        (∀ i j, |ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis n.val i j| ≤ c) ∧
        g = k * OperatorExponentialUnits.Construction.operatorExpUnit A.val * n := by
  obtain ⟨K, U, a, hKo, ha, hgap, hU, hbound, hM⟩ := hM
  obtain ⟨k, hk, A, n, hn, he⟩ := d.global_iwasawa hadj hDadj g hg
  have hm : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis k.val *
      Matrix.diagonal (fun i => Real.exp (d.weight i A)) *
      ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis n.val = K * Matrix.diagonal a * U := by
    rw [← d.exponential_matrix A]
    change ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis k.val *
      ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis (OperatorExponentialUnits.Construction.operatorExpUnit A.val).val *
      ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis n.val = _
    rw [← map_mul, ← map_mul]
    have hev : g.val = k.val * (OperatorExponentialUnits.Construction.operatorExpUnit A.val).val * n.val := congrArg Units.val he
    rw [← hev]
    exact hM
  obtain ⟨_, hae, hne⟩ := MatrixKANUniqueness.Construction.matrix_kan_factorization_unique _ K _ U
    (fun i => Real.exp (d.weight i A)) a (OrthogonalOperatorMatrices.Construction.orthogonalBracketUnit_matrix d.basis B k hk)
    hKo (fun i => Real.exp_pos _) ha (d.ordered_unipotent_matrix_upper hd ⟨n, hn⟩) hU hm
  refine ⟨k, hk, A, d.chamber_of_exponential_adjacent_bounds hK hd A ?_, n, hn, ?_, he⟩
  · intro i j hij
    rw [congrFun hae i, congrFun hae j]
    exact hgap i j hij
  · intro i j
    rw [hne]
    exact hbound i j

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
