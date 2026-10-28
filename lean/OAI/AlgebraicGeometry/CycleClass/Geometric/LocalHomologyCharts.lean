import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalExcision
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Topology.Algebra.Group.Basic

/-! # Local Homology Charts -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomologyCharts.Cycles

noncomputable section

/-!
# Local singular homology in actual manifold charts

The isomorphism below uses the proved local excision theorem on both open
sets of an open partial homeomorphism. Its middle map is induced by the
actual homeomorphism between those sets. Thus the chart comparison has no
assumed local-homology data. Translation then centers a chart whose model is
a topological additive group.
-/

open _root_.CategoryTheory

section OpenPartialHomeomorph

variable {X Y : TopCat.{0}} [T1Space X] [T1Space Y]
variable (e : OpenPartialHomeomorph X Y) (x : X) (hx : x ∈ e.source) (n : ℕ)

/-- Local homology is transported through an actual open partial
homeomorphism, by excising its source and target. -/
def openPartialHomeomorphLocalHomologyIso :
    LocalHomology.Cycles.localSingularHomology X x n ≅ LocalHomology.Cycles.localSingularHomology Y (e x) n :=
  (LocalExcision.Cycles.localExcisionHomologyIso X e.source x hx e.open_source n).symm ≪≫
    LocalHomology.Cycles.localSingularHomologyIso
      (X := TopCat.of e.source) (Y := TopCat.of e.target)
      e.toHomeomorphSourceTarget (⟨x, hx⟩ : e.source) n ≪≫
    LocalExcision.Cycles.localExcisionHomologyIso Y e.target (e x) (e.map_source hx) e.open_target n

/-- The forward chart comparison is precisely inverse source excision,
the homeomorphism map, and forward target excision. -/
theorem openPartialHomeomorphLocalHomologyIso_hom :
    (openPartialHomeomorphLocalHomologyIso e x hx n).hom =
      (LocalExcision.Cycles.localExcisionHomologyIso X e.source x hx e.open_source n).inv ≫
        (LocalHomology.Cycles.localSingularHomologyIso
          (X := TopCat.of e.source) (Y := TopCat.of e.target)
          e.toHomeomorphSourceTarget (⟨x, hx⟩ : e.source) n).hom ≫
        HomologicalComplex.homologyMap
          (LocalExcision.Cycles.localExcisionChainMap Y e.target (e x) (e.map_source hx)) n := rfl

/-- This comparison agrees with the actual chart homeomorphism on classes
represented in the chart source. -/
@[reassoc]
theorem openPartialHomeomorphLocalHomologyIso_source :
    HomologicalComplex.homologyMap (LocalExcision.Cycles.localExcisionChainMap X e.source x hx) n ≫
        (openPartialHomeomorphLocalHomologyIso e x hx n).hom =
      (LocalHomology.Cycles.localSingularHomologyIso
        (X := TopCat.of e.source) (Y := TopCat.of e.target)
        e.toHomeomorphSourceTarget (⟨x, hx⟩ : e.source) n).hom ≫
        HomologicalComplex.homologyMap
          (LocalExcision.Cycles.localExcisionChainMap Y e.target (e x) (e.map_source hx)) n := by
  change (LocalExcision.Cycles.localExcisionHomologyIso X e.source x hx e.open_source n).hom ≫
    (LocalExcision.Cycles.localExcisionHomologyIso X e.source x hx e.open_source n).inv ≫ _ = _
  exact (LocalExcision.Cycles.localExcisionHomologyIso X e.source x hx e.open_source n).hom_inv_id_assoc _

end OpenPartialHomeomorph

section ChartedSpace

variable (H M : Type) [TopologicalSpace H] [TopologicalSpace M]
variable [ChartedSpace H M] [T1Space H]

/-- The local homology of a charted space is the local homology of its
model at the chart image. The T1 property of the space follows from the
actual charts and the T1 property of the model. -/
def chartLocalHomologyIso (x : M) (n : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of M) x n ≅
      LocalHomology.Cycles.localSingularHomology (TopCat.of H) (chartAt H x x) n := by
  letI : T1Space M := ChartedSpace.t1Space H M
  exact openPartialHomeomorphLocalHomologyIso
    (X := TopCat.of M) (Y := TopCat.of H)
    (chartAt H x) x (mem_chart_source H x) n

/-- The chart comparison has the source compatibility of the actual open
partial homeomorphism, with no choice of an unrelated group isomorphism. -/
@[reassoc]
theorem chartLocalHomologyIso_source (x : M) (n : ℕ) :
    HomologicalComplex.homologyMap
        (LocalExcision.Cycles.localExcisionChainMap (TopCat.of M) (chartAt H x).source x
          (mem_chart_source H x)) n ≫
        (chartLocalHomologyIso H M x n).hom =
      (LocalHomology.Cycles.localSingularHomologyIso
        (X := TopCat.of (chartAt H x).source) (Y := TopCat.of (chartAt H x).target)
        (chartAt H x).toHomeomorphSourceTarget
        (⟨x, mem_chart_source H x⟩ : (chartAt H x).source) n).hom ≫
        HomologicalComplex.homologyMap
          (LocalExcision.Cycles.localExcisionChainMap (TopCat.of H) (chartAt H x).target
            (chartAt H x x) (mem_chart_target H x)) n := by
  have : T1Space M := ChartedSpace.t1Space H M
  exact openPartialHomeomorphLocalHomologyIso_source
    (X := TopCat.of M) (Y := TopCat.of H)
    (chartAt H x) x (mem_chart_source H x) n

end ChartedSpace

variable (E : Type) [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]

/-- Translation by `-x` identifies local homology at `x` with local
homology at the origin of a topological additive group. -/
def translationLocalHomologyIso (x : E) (n : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of E) x n ≅
      LocalHomology.Cycles.localSingularHomology (TopCat.of E) (0 : E) n := by
  simpa only [Homeomorph.coe_addLeft, neg_add_cancel] using
    (LocalHomology.Cycles.localSingularHomologyIso (X := TopCat.of E) (Y := TopCat.of E)
      (Homeomorph.addLeft (-x)) x n)

variable (M : Type) [TopologicalSpace M] [ChartedSpace E M] [T1Space E]

/-- A chart and translation identify actual local homology with that of
the model at the origin. -/
def centeredChartLocalHomologyIso (x : M) (n : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of M) x n ≅
      LocalHomology.Cycles.localSingularHomology (TopCat.of E) (0 : E) n :=
  chartLocalHomologyIso E M x n ≪≫
    translationLocalHomologyIso E (chartAt E x x) n

@[simp]
theorem centeredChartLocalHomologyIso_hom (x : M) (n : ℕ) :
    (centeredChartLocalHomologyIso E M x n).hom =
      (chartLocalHomologyIso E M x n).hom ≫
        (translationLocalHomologyIso E (chartAt E x x) n).hom := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.LocalHomologyCharts.Cycles
