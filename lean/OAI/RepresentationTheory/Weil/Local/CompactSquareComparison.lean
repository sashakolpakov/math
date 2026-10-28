import OAI.RepresentationTheory.Weil.Local.SquareComparison
import OAI.RepresentationTheory.Weil.Local.NormSquareKernels

/-! # Compact Square Comparison -/

namespace OAI.RepresentationTheory.Weil.Local.CompactSquareComparison.Construction

noncomputable section

/-! Equality of square-class counts in the compact field-unit and nonsplit norm-one groups. -/

open Set

theorem normUnit_normOne_square_index_eq
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [IsUltrametricDist k] (hnd : ¬ DiscreteTopology k) (h : ¬ ∃ t : k, t ^ 2 = -1) :
    (QuadraticNormSubgroup.Construction.squareUnitsSubgroup (PrincipalSquareClasses.Construction.normUnitSubgroup k)).index =
      (QuadraticNormSubgroup.Construction.squareUnitsSubgroup (QuadraticNormAt.Construction.QuadraticNormOne k)).index := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField k with hd | ⟨_, rfl⟩
  · exact (hnd hd).elim
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hnd
  let : CompactSpace (PrincipalSquareClasses.Construction.normUnitSubgroup k) :=
    isCompact_iff_compactSpace.mp PrincipalSquareClasses.Construction.normUnitSubgroup_isCompact
  let : CompactSpace (QuadraticNormAt.Construction.QuadraticNormOne k) := QuadraticNormAt.Construction.quadraticNormOne_compactSpace hnd h
  obtain ⟨r, hr, hr1, hr2, hi⟩ := SquareComparison.Construction.exists_principalNorm_square_index_eq h
  let P := PrincipalSquareClasses.Construction.principalUnitSubgroup (k := k) r hr hr1
  let H := P.subgroupOf (PrincipalSquareClasses.Construction.normUnitSubgroup k)
  let T := NormSmallSubgroup.Construction.normSmallSubgroup h r hr hr1
  have hHopen : IsOpen (H : Set (PrincipalSquareClasses.Construction.normUnitSubgroup k)) :=
    Subgroup.subgroupOf_isOpen _ _ (PrincipalSquareClasses.Construction.principalUnitSubgroup_isOpen r hr hr1)
  have hTopen : IsOpen (T : Set (QuadraticNormAt.Construction.QuadraticNormOne k)) := NormSmallSubgroup.Construction.normSmallSubgroup_isOpen h r hr hr1
  have hHfinite : H.index ≠ 0 := by
    let : Finite ((PrincipalSquareClasses.Construction.normUnitSubgroup k) ⧸ H) := H.quotient_finite_of_isOpen hHopen
    exact H.index_ne_zero_of_finite
  have hTfinite : T.index ≠ 0 := by
    let : Finite ((QuadraticNormAt.Construction.QuadraticNormOne k) ⧸ T) := T.quotient_finite_of_isOpen hTopen
    exact T.index_ne_zero_of_finite
  apply SquareIndexTools.Construction.square_index_eq_of_local_indices H T hHfinite hTfinite
  · intro x hx hx2
    apply Subtype.ext
    exact PrincipalSquareClasses.Construction.principalUnitSubgroup_no_two_torsion r hr hr1 hr2 x.val hx (congrArg Subtype.val hx2)
  · exact NormSmallSubgroup.Construction.normSmallSubgroup_no_two_torsion h r hr hr1
  · rw [NormSquareKernels.Construction.normUnit_square_kernel_card, NormSquareKernels.Construction.normOne_square_kernel_card]
  · have he := SquareIndexTools.Construction.square_index_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (PrincipalSquareClasses.Construction.principalUnitSubgroup_le_normUnitSubgroup (k := k) r hr hr1))
    exact he.trans hi

end

end OAI.RepresentationTheory.Weil.Local.CompactSquareComparison.Construction
