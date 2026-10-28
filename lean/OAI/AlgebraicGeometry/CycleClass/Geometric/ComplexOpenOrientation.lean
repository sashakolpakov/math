import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexCoordinateComparison
import Mathlib.Geometry.Manifold.HasGroupoid

/-! # Complex Open Orientation -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexOpenOrientation

noncomputable section

/-!
# Canonical complex local classes under open inclusions

The inherited chart on an open subspace is the ambient chart restricted to
that subspace. The actual local excision map therefore commutes with the
centered chart isomorphisms. This proves that it carries the canonical local
complex class to the ambient canonical class.
-/

open _root_.CategoryTheory _root_.TopologicalSpace
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Cycles

section InheritedCharts

variable {E : Type} [NormedAddCommGroup E]
variable {M : Type} [TopologicalSpace M] [ChartedSpace E M]

/-- Centering the inherited open-subspace chart gives the inclusion
followed by the centered ambient chart, as actual partial homeomorphisms. -/
theorem centeredChartAt_open_eq (U : Opens M) (x : U) :
    CenteredChartTransition.Cycles.centeredLocalChart (chartAt E x) x =
      (U.openPartialHomeomorphSubtypeCoe ⟨x⟩).trans
        (CenteredChartTransition.Cycles.centeredLocalChart (chartAt E x.val) x.val) := by
  unfold CenteredChartTransition.Cycles.centeredLocalChart
  rw [Opens.chartAt_eq, OpenPartialHomeomorph.subtypeRestr_def,
    OpenPartialHomeomorph.trans_transHomeomorph]
  rfl

end InheritedCharts

variable {M : Type} [TopologicalSpace M] [T1Space M]

/-- The excision isomorphism of an open inclusion is its actual local
partial-homeomorphism isomorphism. -/
theorem localExcisionHomologyIso_eq_subtypePartial (U : Opens M) (x : U) (n : ℕ) :
    (LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of M) (U : Set M) x.val x.property U.isOpen n).hom =
      (LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo (X := TopCat.of U) (Y := TopCat.of M)
        (U.openPartialHomeomorphSubtypeCoe ⟨x⟩) x x.val
        (by change x ∈ Set.univ; trivial) rfl n).hom := by
  exact (LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_eq_map
    (X := TopCat.of U) (Y := TopCat.of M)
    (U.openPartialHomeomorphSubtypeCoe ⟨x⟩)
    (LocalHomology.Cycles.subspaceInclusion (TopCat.of M) (U : Set M)) Subtype.val_injective
    x x.val (by change x ∈ Set.univ; trivial) rfl rfl (fun _ _ => rfl) n).symm

variable {p : ℕ} [ChartedSpace (Fin p → ℂ) M]

/-- The genuine open-inclusion map commutes with the actual centered
chart local homology isomorphisms. -/
@[reassoc]
theorem complexChartLocalIso_open_naturality (U : Opens M) (x : U) (n : ℕ) :
    (LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of M) (U : Set M) x.val x.property U.isOpen n).hom ≫
        (ComplexChartOrientation.Cycles.complexChartLocalIso (chartAt (Fin p → ℂ) x.val) x.val
          (mem_chart_source (Fin p → ℂ) x.val) n).hom =
      (ComplexChartOrientation.Cycles.complexChartLocalIso (chartAt (Fin p → ℂ) x) x
        (mem_chart_source (Fin p → ℂ) x) n).hom := by
  rw [localExcisionHomologyIso_eq_subtypePartial]
  have hi : x ∈ (U.openPartialHomeomorphSubtypeCoe ⟨x⟩).source := by
    change x ∈ Set.univ
    trivial
  have hm : x.val ∈ (CenteredChartTransition.Cycles.centeredLocalChart (chartAt (Fin p → ℂ) x.val) x.val).source := by
    rw [CenteredChartTransition.Cycles.centeredLocalChart_source]
    exact mem_chart_source (Fin p → ℂ) x.val
  have hu : x ∈ (CenteredChartTransition.Cycles.centeredLocalChart (chartAt (Fin p → ℂ) x) x).source := by
    rw [CenteredChartTransition.Cycles.centeredLocalChart_source]
    exact mem_chart_source (Fin p → ℂ) x
  change (LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo (X := TopCat.of U) (Y := TopCat.of M)
      (U.openPartialHomeomorphSubtypeCoe ⟨x⟩) x x.val hi rfl n).hom ≫
        (LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo (X := TopCat.of M) (Y := TopCat.of (Fin p → ℂ))
          (CenteredChartTransition.Cycles.centeredLocalChart (chartAt (Fin p → ℂ) x.val) x.val) x.val 0 hm
          (CenteredChartTransition.Cycles.centeredLocalChart_at_point _ _) n).hom =
      (LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo (X := TopCat.of U) (Y := TopCat.of (Fin p → ℂ))
        (CenteredChartTransition.Cycles.centeredLocalChart (chartAt (Fin p → ℂ) x) x) x 0 hu
        (CenteredChartTransition.Cycles.centeredLocalChart_at_point _ _) n).hom
  rw [LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_comp]
  exact congrArg Iso.hom (LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_congr
    (X := TopCat.of U) (Y := TopCat.of (Fin p → ℂ))
    (centeredChartAt_open_eq (E := Fin p → ℂ) U x).symm x 0 _ _ _ _ n)

variable [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 M]

/-- The canonical local complex class on an open submanifold maps to the
ambient canonical class under the actual local excision isomorphism. -/
theorem complexCanonicalLocalClass_open_inclusion (U : Opens M) (x : U) :
    (LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of M) (U : Set M) x.val x.property
      U.isOpen (2 * p)).hom (ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x) =
        ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x.val := by
  apply (ConcreteCategory.bijective_of_isIso
    (ComplexChartOrientation.Cycles.complexChartLocalIso (chartAt (Fin p → ℂ) x.val) x.val
      (mem_chart_source (Fin p → ℂ) x.val) (2 * p)).hom).1
  change ((LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of M) (U : Set M) x.val x.property
      U.isOpen (2 * p)).hom ≫
        (ComplexChartOrientation.Cycles.complexChartLocalIso (chartAt (Fin p → ℂ) x.val) x.val
          (mem_chart_source (Fin p → ℂ) x.val) (2 * p)).hom)
      (ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x) = _
  rw [complexChartLocalIso_open_naturality]
  exact (ComplexChartOrientation.Cycles.complexChartLocalIso_canonical (p := p) (M := U)
    (chartAt (Fin p → ℂ) x) (chart_mem_atlas (Fin p → ℂ) x) x
    (mem_chart_source (Fin p → ℂ) x)).trans
      (ComplexChartOrientation.Cycles.complexChartLocalIso_canonical (p := p) (M := M)
        (chartAt (Fin p → ℂ) x.val) (chart_mem_atlas (Fin p → ℂ) x.val) x.val
        (mem_chart_source (Fin p → ℂ) x.val)).symm

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexOpenOrientation
