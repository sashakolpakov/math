import OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FilteredBracketGroup
import OAI.NumberTheory.ArithmeticGroups.Lattices.CommutingFilteredUnits
import OAI.NumberTheory.ArithmeticGroups.Lattices.UnipotentFilteredUnits

/-! # Filtered Factor Inclusions -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FilteredFactorInclusions.Construction

noncomputable section

/-! The split exponential and unipotent factors lie in the closed
split-filtered bracket subgroup. -/

open scoped Classical _root_.Matrix.Norms.Operator

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem commutingExponentialSubgroup_le_splitFiltered {m : ℕ}
    (B : L →L[ℝ] L →L[ℝ] L) (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ)
    (H : L →L[ℝ] L) (a : Submodule ℝ (L →L[ℝ] L))
    (ha : a ≤ RegularSymmetricDerivation.Construction.symmetricDerivationSubmodule B) (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y)
    (hH : H ∈ a) (heig : ∀ i, H (b i) = w i • b i) :
    CommutingExponentialSubgroup.Construction.commutingExponentialSubgroup a hc ≤ FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B b.toBasis w a hc := by
  let : CompleteSpace L := FiniteDimensional.complete ℝ L
  let : NormedAlgebra ℚ (L →L[ℝ] L) := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  intro g hg
  have hgB := CommutingExponentialSubgroup.Construction.commutingExponentialSubgroup_le_bracket B a ha hc hg
  obtain ⟨X, rfl⟩ := hg
  have hHX : Commute H X.toAdd.val := hc H hH X.toAdd.val X.toAdd.property
  have hHg : Commute H (CommutingExponentialSubgroup.Construction.commutingExponentialHom a hc X : L →L[ℝ] L) := hHX.exp_right
  have hF := CommutingFilteredUnits.Construction.commuting_unit_mem_weightFiltered b w H (ha hH).1 heig (CommutingExponentialSubgroup.Construction.commutingExponentialHom a hc X) hHg
  apply (FilteredBracketGroup.Construction.mem_splitFilteredBracketUnitGroup_iff B b.toBasis w a hc _).mpr
  refine ⟨hgB, hF, ?_⟩
  rw [CommutingFilteredUnits.Construction.commuting_unit_weightBlockProjection_eq b w H (ha hH).1 heig _ hHg]
  exact ⟨X, rfl⟩

theorem unipotentBracketUnitGroup_le_splitFiltered {m : ℕ}
    (B : L →L[ℝ] L →L[ℝ] L) (b : OrthonormalBasis (Fin m) ℝ L) (w : Fin m → ℝ)
    (a : Submodule ℝ (L →L[ℝ] L)) (hc : ∀ X ∈ a, ∀ Y ∈ a, Commute X Y) :
    UnipotentBracketGroup.Construction.unipotentBracketUnitGroup B b w ≤ FilteredBracketGroup.Construction.splitFilteredBracketUnitGroup B b.toBasis w a hc := by
  intro g hg
  have hF := UnipotentFilteredUnits.Construction.weightRaisingUnitGroup_le_filtered b w hg.2
  apply (FilteredBracketGroup.Construction.mem_splitFilteredBracketUnitGroup_iff B b.toBasis w a hc g).mpr
  refine ⟨hg.1, hF, ?_⟩
  rw [UnipotentFilteredUnits.Construction.weightRaising_unit_blockProjection_eq_one b w _ hg.2]
  exact Subgroup.one_mem _

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Split.FilteredFactorInclusions.Construction
