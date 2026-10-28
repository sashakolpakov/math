import OAI.RepresentationTheory.Theta.Geometric.CompactLattice
import OAI.NumberTheory.ArithmeticGroups.Data

/-! # Data -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus.Data.CM

noncomputable section

/-!
Data already constructed before algebraization: a finite-dimensional complex
vector space, a discrete full integer lattice, and the analytic projective
embedding supplied by the reference analytic fiber. No algebraic variety,
Hodge realization, or cohomological comparison is a field of this structure.
-/

structure ProjectivePeriodData where
  space : Type
  [normed : NormedAddCommGroup space]
  [complex : NormedSpace ℂ space]
  [real : NormedSpace ℝ space]
  [tower : IsScalarTower ℝ ℂ space]
  [finite : FiniteDimensional ℂ space]
  periodIntegerLattice : Submodule ℤ space
  [periodIntegerLattice_discrete : DiscreteTopology periodIntegerLattice]
  [periodIntegerLattice_full : IsZLattice ℝ periodIntegerLattice]
  projective : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.IsProjectiveComplexTorus space periodIntegerLattice.toAddSubgroup

attribute [instance] ProjectivePeriodData.normed ProjectivePeriodData.complex
  ProjectivePeriodData.real ProjectivePeriodData.tower ProjectivePeriodData.finite
  ProjectivePeriodData.periodIntegerLattice_discrete ProjectivePeriodData.periodIntegerLattice_full

namespace ProjectivePeriodData

def ofCompactProjectiveTorus
    (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
    [IsScalarTower ℝ ℂ V] [FiniteDimensional ℂ V]
    (L : AddSubgroup V) [DiscreteTopology L] [CompactSpace (V ⧸ L)]
    (hprojective : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.IsProjectiveComplexTorus V L) : ProjectivePeriodData := by
  let : FiniteDimensional ℝ V := FiniteDimensional.trans ℝ ℂ V
  let : DiscreteTopology L.toIntSubmodule := inferInstanceAs (DiscreteTopology L)
  let : CompactSpace (V ⧸ L.toIntSubmodule.toAddSubgroup) := by
    change CompactSpace (V ⧸ L)
    infer_instance
  exact {
    space := V
    periodIntegerLattice := L.toIntSubmodule
    periodIntegerLattice_full := CompactLattice.isZLattice_of_compact_quotient L.toIntSubmodule
    projective := by
      change NumberTheory.ArithmeticGroups.Data.CongruenceLevel.IsProjectiveComplexTorus V L
      exact hprojective }

instance realFinite (D : ProjectivePeriodData) : FiniteDimensional ℝ D.space :=
  FiniteDimensional.trans ℝ ℂ D.space

abbrev periodTorus (D : ProjectivePeriodData) :=
  D.space ⧸ D.periodIntegerLattice.toAddSubgroup

instance periodTorus_compact (D : ProjectivePeriodData) : CompactSpace D.periodTorus := by
  apply isCompact_univ_iff.mp
  have hc := IsZLattice.isCompact_range_of_periodic D.periodIntegerLattice
    (QuotientAddGroup.mk : D.space → D.periodTorus)
    QuotientAddGroup.continuous_mk (by
      intro z w hw
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff w).mpr hw, add_zero])
  rwa [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] at hc

instance periodTorus_t2 (D : ProjectivePeriodData) : T2Space D.periodTorus := by
  let : DiscreteTopology D.periodIntegerLattice.toAddSubgroup :=
    D.periodIntegerLattice_discrete
  let : IsClosed (D.periodIntegerLattice.toAddSubgroup : Set D.space) :=
    AddSubgroup.isClosed_of_discreteTopology
  infer_instance

end ProjectivePeriodData

end

end OAI.RepresentationTheory.Theta.Geometric.Torus.Data.CM
