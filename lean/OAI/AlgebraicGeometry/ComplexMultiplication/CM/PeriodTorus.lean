import OAI.AlgebraicGeometry.ComplexMultiplication.CM.PeriodRiemannForm
import Mathlib.Topology.Covering.Quotient
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Convex.Topology

/-! # Period Torus -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CM

noncomputable section

/-!
# The complex manifold underlying the CM period torus

The quotient projection is a covering map. Local inverses give charts on the
compact Hausdorff quotient. Changes of charts are locally translations by
lattice elements, so they are complex smooth. The resulting complex manifold
uses the topology and the actual quotient constructed in `CMPeriodSpace`.
This does not yet construct an algebraic projective realization.
-/

open scoped Classical _root_.NumberField ContDiff
open _root_.Topology Filter

open _root_.NumberField

variable {E : Type*} [Field E] [NumberField E] [Algebra ℚ E] [IsCMField E]

variable (ε : TypeHodgeStructure.CMEmbeddingType E)

/-- The period projection is a covering by the discrete group of lattice translations. -/
theorem TypeHodgeStructure.CMEmbeddingType.periodProjection_isCoveringMap :
    IsCoveringMap (QuotientAddGroup.mk : PeriodSpace.CMPeriodSpace E → ε.periodTorus) := by
  apply (ε.periodIntegerLattice.toAddSubgroup.isAddQuotientCoveringMap_of_comm _).isCoveringMap
  exact isDiscrete_iff_discreteTopology.mpr ε.periodIntegerLattice_discrete

/-- A representative used only to choose a local chart at each quotient point. -/
def TypeHodgeStructure.CMEmbeddingType.periodRepresentative (q : ε.periodTorus) : PeriodSpace.CMPeriodSpace E :=
  (QuotientAddGroup.mk_surjective q).choose

theorem TypeHodgeStructure.CMEmbeddingType.periodRepresentative_mk (q : ε.periodTorus) :
    QuotientAddGroup.mk (ε.periodRepresentative q) = q :=
  (QuotientAddGroup.mk_surjective q).choose_spec

/-- A local inverse of the actual period projection. -/
def TypeHodgeStructure.CMEmbeddingType.periodChart (q : ε.periodTorus) : OpenPartialHomeomorph ε.periodTorus (PeriodSpace.CMPeriodSpace E) :=
  ε.periodProjection_isCoveringMap.isLocalHomeomorph.localInverseAt (ε.periodRepresentative q)

theorem TypeHodgeStructure.CMEmbeddingType.periodChart_symm (q : ε.periodTorus) :
    ⇑(ε.periodChart q).symm = (QuotientAddGroup.mk : PeriodSpace.CMPeriodSpace E → ε.periodTorus) :=
  ε.periodProjection_isCoveringMap.isLocalHomeomorph.localInverseAt_symm _

theorem TypeHodgeStructure.CMEmbeddingType.mem_periodChart_source (q : ε.periodTorus) : q ∈ (ε.periodChart q).source := by
  have h := ε.periodProjection_isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source
    (x := ε.periodRepresentative q)
  simpa only [TypeHodgeStructure.CMEmbeddingType.periodChart, ε.periodRepresentative_mk] using h

instance TypeHodgeStructure.CMEmbeddingType.periodTorus_chartedSpace : ChartedSpace (PeriodSpace.CMPeriodSpace E) ε.periodTorus where
  atlas := Set.range ε.periodChart
  chartAt := ε.periodChart
  mem_chart_source := ε.mem_periodChart_source
  chart_mem_atlas q := ⟨q, rfl⟩

theorem TypeHodgeStructure.CMEmbeddingType.period_extChart (q : ε.periodTorus) :
    ⇑(extChartAt (modelWithCornersSelf ℂ (PeriodSpace.CMPeriodSpace E)) q) = ε.periodChart q := rfl

theorem TypeHodgeStructure.CMEmbeddingType.period_extChart_symm (q : ε.periodTorus) :
    ⇑(extChartAt (modelWithCornersSelf ℂ (PeriodSpace.CMPeriodSpace E)) q).symm =
      (QuotientAddGroup.mk : PeriodSpace.CMPeriodSpace E → ε.periodTorus) := by
  change ⇑(ε.periodChart q).symm = _
  exact ε.periodChart_symm q

/-- Every local inverse of the projection is locally a translation after precomposition
with the projection. -/
theorem TypeHodgeStructure.CMEmbeddingType.periodSection_eventuallyEq (e : OpenPartialHomeomorph ε.periodTorus (PeriodSpace.CMPeriodSpace E))
    (he : ⇑e.symm = (QuotientAddGroup.mk : PeriodSpace.CMPeriodSpace E → ε.periodTorus))
    (z : PeriodSpace.CMPeriodSpace E) (hz : QuotientAddGroup.mk z ∈ e.source) :
    (fun w : PeriodSpace.CMPeriodSpace E => e (QuotientAddGroup.mk w)) =ᶠ[𝓝 z]
      (fun w => w + (e (QuotientAddGroup.mk z) - z)) := by
  let c : PeriodSpace.CMPeriodSpace E := e (QuotientAddGroup.mk z) - z
  have hc : (QuotientAddGroup.mk c : ε.periodTorus) = 0 := by
    change (QuotientAddGroup.mk (e (QuotientAddGroup.mk z) - z) : ε.periodTorus) = 0
    have hq := e.left_inv hz
    rw [he] at hq
    rw [QuotientAddGroup.mk_sub, hq, sub_self]
  have hn : ∀ᶠ w in 𝓝 z, w + c ∈ e.target := by
    apply (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds
    apply e.open_target.mem_nhds
    change z + c ∈ e.target
    simpa [c, add_comm] using e.map_source hz
  change (fun w : PeriodSpace.CMPeriodSpace E => e (QuotientAddGroup.mk w)) =ᶠ[𝓝 z]
      (fun w => w + c)
  filter_upwards [hn] with w hw
  have hq : (QuotientAddGroup.mk (w + c) : ε.periodTorus) = QuotientAddGroup.mk w := by
    rw [QuotientAddGroup.mk_add, hc, add_zero]
  rw [← hq, ← he]
  exact e.right_inv hw

/-- Local translations are complex smooth. -/
theorem TypeHodgeStructure.CMEmbeddingType.periodSection_contDiffAt (e : OpenPartialHomeomorph ε.periodTorus (PeriodSpace.CMPeriodSpace E))
    (he : ⇑e.symm = (QuotientAddGroup.mk : PeriodSpace.CMPeriodSpace E → ε.periodTorus))
    (z : PeriodSpace.CMPeriodSpace E) (hz : QuotientAddGroup.mk z ∈ e.source) :
    ContDiffAt ℂ ∞ (fun w : PeriodSpace.CMPeriodSpace E => e (QuotientAddGroup.mk w)) z :=
  (contDiffAt_id.add contDiffAt_const).congr_of_eventuallyEq
    (ε.periodSection_eventuallyEq e he z hz)

/-- The compact period quotient carries the complex manifold structure defined by its charts. -/
instance TypeHodgeStructure.CMEmbeddingType.periodTorus_isManifold :
    IsManifold (modelWithCornersSelf ℂ (PeriodSpace.CMPeriodSpace E)) ∞ ε.periodTorus := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨q, rfl⟩ := he
  obtain ⟨q', rfl⟩ := he'
  intro z hz
  have hz' : QuotientAddGroup.mk z ∈ (ε.periodChart q').source := by
    have ht : (ε.periodChart q).symm z ∈ (ε.periodChart q').source := hz.1.2
    simpa only [ε.periodChart_symm] using ht
  have hs := ε.periodSection_contDiffAt (ε.periodChart q') (ε.periodChart_symm q') z hz'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_def,
    OpenPartialHomeomorph.coe_trans, ε.periodChart_symm, id_eq] using hs.contDiffWithinAt

/-- The covering projection is complex smooth for the constructed manifold structure. -/
theorem TypeHodgeStructure.CMEmbeddingType.periodProjection_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ (PeriodSpace.CMPeriodSpace E))
      (modelWithCornersSelf ℂ (PeriodSpace.CMPeriodSpace E)) ∞
      (QuotientAddGroup.mk : PeriodSpace.CMPeriodSpace E → ε.periodTorus) := by
  intro z
  apply contMDiffAt_iff_target.mpr
  refine ⟨QuotientAddGroup.continuous_mk.continuousAt, ?_⟩
  have hs := ε.periodSection_contDiffAt (ε.periodChart (QuotientAddGroup.mk z))
    (ε.periodChart_symm _) z (ε.mem_periodChart_source _)
  simpa only [ε.period_extChart, Function.comp_def] using hs.contMDiffAt

/-- Smoothness of a map out of the quotient can be checked after lifting along the projection. -/
theorem TypeHodgeStructure.CMEmbeddingType.contMDiff_of_periodProjection {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {M : Type*} [TopologicalSpace M] [ChartedSpace F M]
    (f : ε.periodTorus → M)
    (hf : ContMDiff (modelWithCornersSelf ℂ (PeriodSpace.CMPeriodSpace E)) (modelWithCornersSelf ℂ F) ∞
      (fun z : PeriodSpace.CMPeriodSpace E => f (QuotientAddGroup.mk z))) :
    ContMDiff (modelWithCornersSelf ℂ (PeriodSpace.CMPeriodSpace E)) (modelWithCornersSelf ℂ F) ∞ f := by
  intro q
  apply contMDiffAt_iff_source.mpr
  simpa only [ε.period_extChart_symm, Function.comp_def] using
    (hf (extChartAt (modelWithCornersSelf ℂ (PeriodSpace.CMPeriodSpace E)) q q)).contMDiffWithinAt

instance TypeHodgeStructure.CMEmbeddingType.periodTorus_contMDiffAdd :
    ContMDiffAdd (modelWithCornersSelf ℂ (PeriodSpace.CMPeriodSpace E)) ∞ ε.periodTorus where
  contMDiff_add := by
    intro p
    let : ChartedSpace (PeriodSpace.CMPeriodSpace E × PeriodSpace.CMPeriodSpace E) (PeriodSpace.CMPeriodSpace E × PeriodSpace.CMPeriodSpace E) :=
      chartedSpaceSelf _
    apply contMDiffAt_iff_source.mpr
    have hf : ContMDiff
        (modelWithCornersSelf ℂ (PeriodSpace.CMPeriodSpace E × PeriodSpace.CMPeriodSpace E))
        (modelWithCornersSelf ℂ (PeriodSpace.CMPeriodSpace E)) ∞
        (fun z : PeriodSpace.CMPeriodSpace E × PeriodSpace.CMPeriodSpace E =>
          (QuotientAddGroup.mk (z.1 + z.2) : ε.periodTorus)) :=
      ε.periodProjection_contMDiff.comp (contDiff_fst.add contDiff_snd).contMDiff
    simpa only [extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe,
      ε.period_extChart_symm, Function.comp_def, Prod.map_apply, QuotientAddGroup.mk_add] using
      (hf ((extChartAt ((modelWithCornersSelf ℂ (PeriodSpace.CMPeriodSpace E)).prod
        (modelWithCornersSelf ℂ (PeriodSpace.CMPeriodSpace E))) p) p)).contMDiffWithinAt

/-- The actual compact complex manifold quotient is a complex Lie group. -/
instance TypeHodgeStructure.CMEmbeddingType.periodTorus_lieAddGroup :
    LieAddGroup (modelWithCornersSelf ℂ (PeriodSpace.CMPeriodSpace E)) ∞ ε.periodTorus where
  contMDiff_neg := by
    apply ε.contMDiff_of_periodProjection
    have hf : ContMDiff (modelWithCornersSelf ℂ (PeriodSpace.CMPeriodSpace E))
        (modelWithCornersSelf ℂ (PeriodSpace.CMPeriodSpace E)) ∞
        (fun z : PeriodSpace.CMPeriodSpace E => (QuotientAddGroup.mk (-z) : ε.periodTorus)) :=
      ε.periodProjection_contMDiff.comp contMDiff_id.neg
    simpa only [QuotientAddGroup.mk_neg] using hf

instance TypeHodgeStructure.CMEmbeddingType.periodTorus_connected : ConnectedSpace ε.periodTorus := by
  exact QuotientAddGroup.mk_surjective.connectedSpace QuotientAddGroup.continuous_mk

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CM
