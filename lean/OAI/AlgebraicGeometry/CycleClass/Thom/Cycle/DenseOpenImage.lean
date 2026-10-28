import OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Open
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion

/-! # Dense Open Image -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.DenseOpenImage.Constructions

noncomputable section

/-! An actual open immersion into a cycle support has the full cycle image on the complement of its omitted boundary. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.ProperImage.Open.Constructions.Construction OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.RegularOpenImmersion.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (D : Geometric.DimensionCycles.DimensionCycleSupport V p)
  {T : Over Foundations.Scheme.ProjectiveSpace.complexBase} (j : T ⟶ D.toOver) [IsOpenImmersion j.left]
  (U : Opens V.analyticSpace)
  (hU : (U : Set V.analyticSpace) ⊆ ProperImage.CompactProjection.Constructions.Construction.algebraicComplementOpen V (ProperImage.Open.Constructions.Construction.supportOpenBoundary D j.left.opensRange))

include hU in
theorem supportOpenImmersion_range :
    ((Subtype.val : U → V.analyticSpace) ⁻¹' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (j ≫ D.toAmbient))) =
      (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion := by
  ext y
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j x, (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp j D.toAmbient x).symm.trans hx⟩
  · rintro ⟨x, hx⟩
    have hxb : D.analyticInclusion x ∈ ProperImage.CompactProjection.Constructions.Construction.algebraicComplementOpen V (ProperImage.Open.Constructions.Construction.supportOpenBoundary D j.left.opensRange) :=
      hx.symm ▸ hU y.property
    have hxW := ProperImage.Open.Constructions.Construction.supportPoint_mem_open_of_boundaryComplement D j.left.opensRange x hxb
    have hr : x ∈ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map j) := by
      rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_map_of_isImmersion j]
      exact hxW
    obtain ⟨z, hz⟩ := hr
    refine ⟨z, ?_⟩
    rw [ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map_comp, hz]
    exact hx

include hU in
theorem supportOpenImmersion_regularImage
    (hR : (U : Set V.analyticSpace) ⊆ D.regularAmbientOpen) :
    ((Subtype.val : U → V.analyticSpace) ⁻¹' Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (j ≫ D.toAmbient))) =
      Set.range (RegularOpenImmersion.Constructions.regularOpenImmersion D U hR) :=
  (supportOpenImmersion_range D j U hU).trans (RegularOpenImmersion.Constructions.regularOpenImmersion_range D U hR).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.DenseOpenImage.Constructions
