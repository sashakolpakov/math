import OAI.NumberTheory.ArithmeticGroups.Lattices.OrderedTriangularCompatibility
import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ChamberIntegrability

/-! # Weights As Differences -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Faithfulness of the adjoint representation realizes each positive
intrinsic weight as an upper-triangular difference of ambient weights. -/

open scoped Classical

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
  {B : L →L[ℝ] L →L[ℝ] L}

theorem KillingSplit.Construction.KillingSplitWeightData.weight_eq_difference
    (d : KillingSplit.Construction.KillingSplitWeightData B) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (r : Fin (Module.finrank ℝ L)) :
    ∃ i j, d.weight r = d.weight i - d.weight j := by
  let X := B (d.basis r)
  have hX : X ≠ 0 := by
    intro hx
    apply d.basis.toBasis.ne_zero r
    exact (ContinuousInnerDerivations.Construction.continuousKillingBracket_injective B hK) (hx.trans (map_zero B).symm)
  have hM : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis X ≠ 0 := by
    intro hm
    apply hX
    exact (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixAlgEquiv d.basis.toBasis).injective (hm.trans (map_zero _).symm)
  have hex : ∃ i j, ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis X i j ≠ 0 := by
    by_contra! h
    exact hM (Matrix.ext h)
  obtain ⟨i, j, hij⟩ := hex
  rw [OperatorWeightMatrix.Construction.continuousEndMatrix_orthonormal_apply] at hij
  refine ⟨i, j, ?_⟩
  apply LinearMap.ext
  intro A
  have he := Positive.DerivationNilpotence.Construction.commutator_eigen_coordinate d.basis A.val (d.le_symmetric A.property).1
    (fun q => d.weight q A) (fun q => d.eigenvector q A) X i j
  have hc : A.val * X - X * A.val = d.weight r A • X := by
    rw [show X = B (d.basis r) from rfl,
      FaithfulDerivationCommutator.Construction.derivation_commutator_inner_operator B A.val (d.le_symmetric A.property).2,
      d.eigenvector, map_smul]
  rw [hc] at he
  simp only [smul_apply, map_smul, PiLp.smul_apply, smul_eq_mul] at he
  exact mul_right_cancel₀ hij he

theorem KillingSplit.Construction.KillingSplitWeightData.positive_weight_eq_upper_difference
    (d : KillingSplit.Construction.KillingSplitWeightData B) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hd : Antitone (fun i => d.weight i d.regularElement)) (r : d.PositiveIndex) :
    ∃ i j, i < j ∧ d.weight r.val = d.weight i - d.weight j := by
  obtain ⟨i, j, he⟩ := d.weight_eq_difference hK r.val
  refine ⟨i, j, ?_, he⟩
  by_contra! hij
  have hm := hd hij
  have hp := r.property
  rw [he, LinearMap.sub_apply] at hp
  linarith

theorem KillingSplit.Construction.KillingSplitWeightData.chamber_of_upper_differences
    (d : KillingSplit.Construction.KillingSplitWeightData B) (hK : (ContinuousInnerDerivations.Construction.continuousBracketKillingForm B).Nondegenerate)
    (hd : Antitone (fun i => d.weight i d.regularElement)) (A : d.subspace) (t : ℝ)
    (hA : ∀ i j, i < j → d.weight i A - d.weight j A ≤ t) :
    A ∈ d.truncatedNegativeChamber t := by
  intro r
  obtain ⟨i, j, hij, he⟩ := d.positive_weight_eq_upper_difference hK hd r
  rw [he, LinearMap.sub_apply]
  exact hA i j hij

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
