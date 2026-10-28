import OAI.NumberTheory.ArithmeticGroups.Lattices.OrderedSplitWeightData
import OAI.NumberTheory.ArithmeticGroups.Lattices.UpperUnitriangularMatrices
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorWeightMatrix
import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentBracketGroup

/-! # Ordered Triangular Compatibility -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices

noncomputable section

/-! Decreasing split weights put positive operators and unipotent
automorphisms into the standard upper-triangular matrix groups. -/

open scoped Classical

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

omit [FiniteDimensional ℝ L] in
theorem OrderedTriangularCompatibility.Construction.ordered_weightRaising_matrix_zero {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (w : Fin m → ℝ) (hw : Antitone w) (X : L →L[ℝ] L) (hX : X ∈ Positive.DerivationNilpotence.Construction.weightRaisingOperators b w)
    (i j : Fin m) (hij : j ≤ i) : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis X i j = 0 :=
  (OperatorWeightMatrix.Construction.weightRaising_matrix_iff b w X).mp hX i j (hw hij)

omit [FiniteDimensional ℝ L] in
theorem OrderedTriangularCompatibility.Construction.ordered_weightRaising_unitriangular {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (w : Fin m → ℝ) (hw : Antitone w) (g : (L →L[ℝ] L)ˣ) (hg : g ∈ UnipotentBracketGroup.Construction.weightRaisingUnitGroup b w) :
    UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val) := by
  have he (i j : Fin m) (hij : j ≤ i) :
      ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val i j - (1 : Matrix (Fin m) (Fin m) ℝ) i j = 0 := by
    have h := OrderedTriangularCompatibility.Construction.ordered_weightRaising_matrix_zero b w hw (g.val - 1) hg i j hij
    simpa only [map_sub, map_one, Matrix.sub_apply] using h
  constructor
  · intro i j hij
    have h := he i j hij.le
    have hij' : i ≠ j := ne_of_gt hij
    rw [Matrix.one_apply, ite_eq_right hij', sub_zero] at h
    exact h
  · intro i
    have h := he i i le_rfl
    rw [Matrix.one_apply_eq] at h
    exact sub_eq_zero.mp h

theorem KillingSplit.Construction.KillingSplitWeightData.ordered_positive_matrix_upper
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B)
    (hd : Antitone (fun i => d.weight i d.regularElement))
    (X : DerivationSpectralDecomposition.Construction.positiveBracketDerivations B d.regularElement.val) :
    (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis X.val).IsUpperTriangular := by
  intro i j hij
  apply OrderedTriangularCompatibility.Construction.ordered_weightRaising_matrix_zero d.basis _ hd X.val _ i j hij.le
  exact Positive.DerivationNilpotence.Construction.positiveBracketDerivations_le_weightRaising B d.basis d.regularElement.val
    (d.le_symmetric d.regularElement.property).1 _ (fun r => d.eigenvector r d.regularElement) X.property

theorem KillingSplit.Construction.KillingSplitWeightData.ordered_unipotent_matrix_upper
    {B : L →L[ℝ] L →L[ℝ] L} (d : KillingSplit.Construction.KillingSplitWeightData B)
    (hd : Antitone (fun i => d.weight i d.regularElement))
    (g : UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B d.basis (fun i => d.weight i d.regularElement)) :
    UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix d.basis.toBasis g.val.val) :=
  OrderedTriangularCompatibility.Construction.ordered_weightRaising_unitriangular d.basis _ hd g.val g.property.2

end

end OAI.NumberTheory.ArithmeticGroups.Lattices
