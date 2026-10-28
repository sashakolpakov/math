import OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnipotentBlockRetraction
import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.BlockDiagonalCommutation
import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.ExponentialMatrixChamber

/-! # Zero Weight Block Centralizer -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! With a regular element separating distinct weights, the
equal-weight unipotent blocks centralize every intrinsic split exponential. -/

open NormedSpace

theorem KillingSplit.Construction.KillingSplitWeightData.zeroWeightBlock_commutes_exponential
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B)
    (hd : Antitone (fun i => d.weight i d.regularElement))
    (hsep : ∀ i j, d.weight i d.regularElement = d.weight j d.regularElement → d.weight i = d.weight j)
    (n : (UpperUnipotentBlockRetraction.Construction.upperUnitriangularBlockProjection (fun i => d.weight i d.regularElement) hd).range)
    (A : d.subspace) :
    Commute n.val.val.val (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis (exp A.val)) := by
  rw [d.exponential_matrix]
  obtain ⟨g, hg⟩ := n.property
  rw [← hg, UpperUnipotentBlockRetraction.Construction.upperUnitriangularBlockProjection_val]
  apply Weight.BlockDiagonalCommutation.Construction.weightBlockProjection_commutes_diagonal
  intro i j hij
  exact congrArg Real.exp (DFunLike.congr_fun (hsep i j hij) A)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
