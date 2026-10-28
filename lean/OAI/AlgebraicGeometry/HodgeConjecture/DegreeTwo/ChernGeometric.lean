import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ThomGeometricComparison
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ConcreteDivisorNeighborhood

/-! # Chern Geometric -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ChernGeometric.Constructions

noncomputable section

/-! Actual first Chern classes and their rational span are represented by the independently constructed geometric cycle-class map. -/

open _root_.CategoryTheory

theorem divisorThom_range_eq_geometric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    LinearMap.range (V.rationalCycleClass 1) = LinearMap.range (V.geometricCycleClassMap 1) := by
  apply le_antisymm
  · rw [V.range_rationalCycleClass]
    apply Submodule.span_le.mpr
    rintro _ ⟨Z, rfl⟩
    refine ⟨Finsupp.single Z (LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension), ?_⟩
    rw [V.geometricCycleClassMap_single]
    exact (ThomGeometricComparison.Constructions.rationalCycleClass_eq_geometric Z).symm
  · rw [V.range_geometricCycleClassMap]
    apply Submodule.span_le.mpr
    rintro _ ⟨Z, rfl⟩
    refine ⟨Finsupp.single Z (LocalProductCoefficient.Constructions.localProductCupCoefficient 1 Z.regularComplexDimension)⁻¹, ?_⟩
    rw [V.rationalCycleClass_single]
    exact (ThomGeometricComparison.Constructions.geometricCycleClass_eq_thom Z).symm

theorem thomCycle_is_geometric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V 1) :
    ∃ w : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V 1, V.geometricCycleClassMap 1 w = V.rationalCycleClass 1 z := by
  have hm : V.rationalCycleClass 1 z ∈ LinearMap.range (V.rationalCycleClass 1) := ⟨z, rfl⟩
  rw [divisorThom_range_eq_geometric V] at hm
  exact hm

theorem firstChernClassQ_is_geometric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (L : DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle V.presentation) :
    ∃ z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V 1,
      V.geometricCycleClassMap 1 z = DivisorClass.Chern.First.firstChernClassQ V.presentation L := by
  obtain ⟨z, hz⟩ := ConcreteDivisorNeighborhood.Constructions.firstChernClassQ_is_Thom_algebraic V L
  obtain ⟨w, hw⟩ := thomCycle_is_geometric V z
  exact ⟨w, hw.trans hz⟩

theorem firstChern_span_is_geometric (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (α : V.rationalCohomology 2)
    (hα : α ∈ Submodule.span ℚ (Set.range (DivisorClass.Chern.First.firstChernClassQ V.presentation))) :
    ∃ z : CycleClass.Geometric.DimensionCycles.RationalDimensionCycle V 1, V.geometricCycleClassMap 1 z = α := by
  obtain ⟨z, hz⟩ := ConcreteDivisorNeighborhood.Constructions.firstChern_span_is_Thom_algebraic V α hα
  obtain ⟨w, hw⟩ := thomCycle_is_geometric V z
  exact ⟨w, hw.trans hz⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.ChernGeometric.Constructions
