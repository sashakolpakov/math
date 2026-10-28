import OAI.RepresentationTheory.Theta.Adelic.QuadraticLocalSquareComparison
import OAI.RepresentationTheory.Weil.Local.FiniteSquareClasses

/-! # Quadratic Norm Index -/

namespace OAI.RepresentationTheory.Theta.Adelic.QuadraticNormIndex

noncomputable section

/-! The norm subgroup has index two for every nonsplit quadratic algebra
over a nonarchimedean local field of characteristic zero. -/

open Set OAI.RepresentationTheory.Weil.Local.FiniteSquareClasses.Construction
open OAI.RepresentationTheory.Theta.Adelic.QuadraticNormSquareQuotient OAI.RepresentationTheory.Theta.Adelic.QuadraticNormChart.Compact

theorem normUnit_normOne_square_index_eq
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [IsUltrametricDist k] (d : k) (hnd : ¬ DiscreteTopology k) (hns : ¬ IsSquare d) :
    (Weil.Local.QuadraticNormSubgroup.Construction.squareUnitsSubgroup (Weil.Local.PrincipalSquareClasses.Construction.normUnitSubgroup k)).index =
      (Weil.Local.QuadraticNormSubgroup.Construction.squareUnitsSubgroup (QuadraticNormSquareQuotient.NormOne d)).index := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField k with hd | ⟨_, rfl⟩
  · exact (hnd hd).elim
  let : ProperSpace k := Weil.Local.FunctionsMetaplectic.Construction.localField_proper k hnd
  let : CompactSpace (Weil.Local.PrincipalSquareClasses.Construction.normUnitSubgroup k) := isCompact_iff_compactSpace.mp Weil.Local.PrincipalSquareClasses.Construction.normUnitSubgroup_isCompact
  let : CompactSpace (QuadraticNormSquareQuotient.NormOne d) := QuadraticNormChart.Compact.normOne_compactSpace d hnd hns
  obtain ⟨r, hr, hr1, hdr, hr2, hi⟩ :=
    QuadraticLocalSquareComparison.exists_principalNorm_square_index_eq d hns
  let P := Weil.Local.PrincipalSquareClasses.Construction.principalUnitSubgroup (k := k) r hr hr1
  let H := P.subgroupOf (Weil.Local.PrincipalSquareClasses.Construction.normUnitSubgroup k)
  let T := QuadraticNormOperations.Small.normSmallSubgroup d hns r hr hr1 hdr
  have hHopen : IsOpen (H : Set (Weil.Local.PrincipalSquareClasses.Construction.normUnitSubgroup k)) :=
    Subgroup.subgroupOf_isOpen _ _ (Weil.Local.PrincipalSquareClasses.Construction.principalUnitSubgroup_isOpen r hr hr1)
  have hTopen : IsOpen (T : Set (QuadraticNormSquareQuotient.NormOne d)) :=
    QuadraticNormOperations.Small.normSmallSubgroup_isOpen d hns r hr hr1 hdr
  have hHfinite : H.index ≠ 0 := by
    let : Finite ((Weil.Local.PrincipalSquareClasses.Construction.normUnitSubgroup k) ⧸ H) := H.quotient_finite_of_isOpen hHopen
    exact H.index_ne_zero_of_finite
  have hTfinite : T.index ≠ 0 := by
    let : Finite ((QuadraticNormSquareQuotient.NormOne d) ⧸ T) := T.quotient_finite_of_isOpen hTopen
    exact T.index_ne_zero_of_finite
  apply Weil.Local.SquareIndexTools.Construction.square_index_eq_of_local_indices H T hHfinite hTfinite
  · intro x hx hx2
    apply Subtype.ext
    exact Weil.Local.PrincipalSquareClasses.Construction.principalUnitSubgroup_no_two_torsion r hr hr1 hr2 x.val hx (congrArg Subtype.val hx2)
  · exact QuadraticNormOperations.Small.normSmallSubgroup_no_two_torsion d hns r hr hr1 hdr
  · rw [Weil.Local.NormSquareKernels.Construction.normUnit_square_kernel_card, QuadraticNormOperations.Small.normOne_square_kernel_card]
  · have he := Weil.Local.SquareIndexTools.Construction.square_index_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (Weil.Local.PrincipalSquareClasses.Construction.principalUnitSubgroup_le_normUnitSubgroup (k := k) r hr hr1))
    exact he.trans hi

theorem normOne_square_index_ne_zero
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [IsUltrametricDist k] (d : k) (hnd : ¬ DiscreteTopology k) (hns : ¬ IsSquare d) :
    (Weil.Local.QuadraticNormSubgroup.Construction.squareUnitsSubgroup (QuadraticNormSquareQuotient.NormOne d)).index ≠ 0 := by
  rw [← normUnit_normOne_square_index_eq d hnd hns]
  exact Weil.Local.FiniteSquareClasses.Construction.normUnit_square_index_ne_zero hnd

theorem squareUnitsSubgroup_le_normRange {k : Type*} [Field k] (d : k) :
    Weil.Local.QuadraticNormSubgroup.Construction.squareUnitsSubgroup kˣ ≤ (QuadraticNormSquareQuotient.normUnits d).range := by
  rintro a ⟨b, rfl⟩
  exact ⟨QuadraticNormSquareQuotient.scalarUnits d b, QuadraticNormSquareQuotient.normUnits_scalar d b⟩

theorem localField_quadraticNorm_index_two
    {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k] [CharZero k]
    [IsUltrametricDist k] (d : k) (hd : d ≠ 0)
    (hnd : ¬ DiscreteTopology k) (hns : ¬ IsSquare d) :
    (QuadraticNormSquareQuotient.normUnits d).range.index = 2 := by
  have hi := Subgroup.relIndex_mul_index (squareUnitsSubgroup_le_normRange d)
  rw [QuadraticNormSquareQuotient.norm_square_relIndex d hd hns, Weil.Local.FiniteSquareClasses.Construction.localField_square_index_eq_twice_normUnit hnd,
    normUnit_normOne_square_index_eq d hnd hns] at hi
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (normOne_square_index_ne_zero d hnd hns))
  exact hi.trans (Nat.mul_comm _ _)

end

end OAI.RepresentationTheory.Theta.Adelic.QuadraticNormIndex
