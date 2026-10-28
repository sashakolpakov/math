import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FilteredFactorInclusions
import OAI.NumberTheory.ArithmeticGroups.Lattices.FilteredOperatorKernel

/-! # Filtered Unipotent Decomposition -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FilteredUnipotentDecomposition.Construction

noncomputable section

/-! Each element of the split-filtered bracket subgroup is a split
exponential times a unipotent bracket automorphism. -/

open scoped Classical _root_.Matrix.Norms.Operator
open NormedSpace

theorem splitFiltered_bracket_decomposition
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (B : L →L[ℝ] L →L[ℝ] L) (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ)
    (H : L →L[ℝ] L) (a : Submodule ℝ (L →L[ℝ] L))
    (ha : a ≤ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B) (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y)
    (hH : H ∈ a) (heig : ∀ i, H (b i) = w i • b i)
    (p : (L →L[ℝ] L)ˣ) (hp : p ∈ FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B b.toBasis w a hc) :
    ∃ X ∈ a, ∃ n ∈ UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B b w, p = OperatorExponentialUnits.Construction.operatorExpUnit X * n := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let : NormedAlgebra ℚ (L →L[ℝ] L) := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  obtain ⟨hpB, hpF, hpA⟩ := (FilteredBracketGroup.Construction.mem_splitFilteredBracketUnitGroup_iff B b.toBasis w a hc p).mp hp
  let q : FilteredOperatorProjection.Construction.weightFilteredOperatorUnits b.toBasis w := ⟨p, hpF⟩
  let π := FilteredOperatorProjection.Construction.weightBlockOperatorUnitProjection b.toBasis w
  let d := π q
  have hdA : d ∈ CommutingExponentialSubgroup.Construction.commutingExponentialSubgroup a hc := hpA
  have hdB := CommutingExponentialSubgroup.Construction.commutingExponentialSubgroup_le_bracket B a ha hc hdA
  obtain ⟨X, hX⟩ := hdA
  have hHd : Commute H (d : L →L[ℝ] L) := by
    rw [← hX]
    exact (hc H hH X.toAdd.val X.toAdd.property).exp_right
  have hdF := CommutingFilteredUnits.Construction.commuting_unit_mem_weightFiltered b w H (ha hH).1 heig d hHd
  let du : FilteredOperatorProjection.Construction.weightFilteredOperatorUnits b.toBasis w := ⟨d, hdF⟩
  have hfix : π du = d := CommutingFilteredUnits.Construction.commuting_unit_weightBlockProjection_eq b w H (ha hH).1 heig du hHd
  let v := du⁻¹ * q
  have hvπ : π v = 1 := by
    change π (du⁻¹ * q) = 1
    rw [map_mul, map_inv, hfix]
    exact inv_mul_cancel d
  have hvW : v.val ∈ UnipotentBracketGroup.Construction.weightRaisingUnitGroup b w := FilteredOperatorKernel.Construction.filtered_unit_mem_weightRaising_of_projection_one b w v hvπ
  have hvB : v.val ∈ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B :=
    (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B).mul_mem ((UnipotentBracketGroup.Construction.continuousBracketUnitGroup B).inv_mem hdB) hpB
  refine ⟨X.toAdd.val, X.toAdd.property, v.val, ⟨hvB, hvW⟩, ?_⟩
  change p = CommutingExponentialSubgroup.Construction.commutingExponentialHom a hc X * (d⁻¹ * p)
  rw [hX, mul_inv_cancel_left]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FilteredUnipotentDecomposition.Construction
