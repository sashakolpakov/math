import OAI.RepresentationTheory.Theta.Geometric.Torus.Data
import Mathlib.Topology.Covering.Quotient
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Convex.Topology

/-! # Manifold -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus

noncomputable section

/-!
# The complex manifold of the generic period torus

The quotient projection is a covering map. Local inverses give charts on the
compact Hausdorff quotient. Changes of charts are locally translations by
lattice elements, so they are complex smooth. The resulting complex manifold
uses the topology and the actual quotient constructed in `CMPeriodSpace`.
Adapted from CMPeriodTorus with its arithmetic assumptions removed.
The input lattice and projective embedding come from the reference analytic fiber.
-/

open scoped Classical ContDiff
open _root_.Topology Filter

variable (ε : Data.CM.ProjectivePeriodData)

/-- The period projection is a covering by the discrete group of lattice translations. -/
theorem Data.CM.ProjectivePeriodData.periodProjection_isCoveringMap :
    IsCoveringMap (QuotientAddGroup.mk : ε.space → ε.periodTorus) := by
  apply (ε.periodIntegerLattice.toAddSubgroup.isAddQuotientCoveringMap_of_comm _).isCoveringMap
  exact isDiscrete_iff_discreteTopology.mpr ε.periodIntegerLattice_discrete

/-- A representative used only to choose a local chart at each quotient point. -/
def Data.CM.ProjectivePeriodData.periodRepresentative (q : ε.periodTorus) : ε.space :=
  (QuotientAddGroup.mk_surjective q).choose

theorem Data.CM.ProjectivePeriodData.periodRepresentative_mk (q : ε.periodTorus) :
    QuotientAddGroup.mk (ε.periodRepresentative q) = q :=
  (QuotientAddGroup.mk_surjective q).choose_spec

/-- A local inverse of the actual period projection. -/
def Data.CM.ProjectivePeriodData.periodChart (q : ε.periodTorus) : OpenPartialHomeomorph ε.periodTorus (ε.space) :=
  ε.periodProjection_isCoveringMap.isLocalHomeomorph.localInverseAt (ε.periodRepresentative q)

theorem Data.CM.ProjectivePeriodData.periodChart_symm (q : ε.periodTorus) :
    ⇑(ε.periodChart q).symm = (QuotientAddGroup.mk : ε.space → ε.periodTorus) :=
  ε.periodProjection_isCoveringMap.isLocalHomeomorph.localInverseAt_symm _

theorem Data.CM.ProjectivePeriodData.mem_periodChart_source (q : ε.periodTorus) : q ∈ (ε.periodChart q).source := by
  have h := ε.periodProjection_isCoveringMap.isLocalHomeomorph.apply_self_mem_localInverseAt_source
    (x := ε.periodRepresentative q)
  simpa only [Data.CM.ProjectivePeriodData.periodChart, ε.periodRepresentative_mk] using h

instance Data.CM.ProjectivePeriodData.periodTorus_chartedSpace : ChartedSpace (ε.space) ε.periodTorus where
  atlas := Set.range ε.periodChart
  chartAt := ε.periodChart
  mem_chart_source := ε.mem_periodChart_source
  chart_mem_atlas q := ⟨q, rfl⟩

theorem Data.CM.ProjectivePeriodData.period_extChart (q : ε.periodTorus) :
    ⇑(extChartAt (modelWithCornersSelf ℂ (ε.space)) q) = ε.periodChart q := rfl

theorem Data.CM.ProjectivePeriodData.period_extChart_symm (q : ε.periodTorus) :
    ⇑(extChartAt (modelWithCornersSelf ℂ (ε.space)) q).symm =
      (QuotientAddGroup.mk : ε.space → ε.periodTorus) := by
  change ⇑(ε.periodChart q).symm = _
  exact ε.periodChart_symm q

/-- Every local inverse of the projection is locally a translation after precomposition
with the projection. -/
theorem Data.CM.ProjectivePeriodData.periodSection_eventuallyEq (e : OpenPartialHomeomorph ε.periodTorus (ε.space))
    (he : ⇑e.symm = (QuotientAddGroup.mk : ε.space → ε.periodTorus))
    (z : ε.space) (hz : QuotientAddGroup.mk z ∈ e.source) :
    (fun w : ε.space => e (QuotientAddGroup.mk w)) =ᶠ[𝓝 z]
      (fun w => w + (e (QuotientAddGroup.mk z) - z)) := by
  let c : ε.space := e (QuotientAddGroup.mk z) - z
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
  change (fun w : ε.space => e (QuotientAddGroup.mk w)) =ᶠ[𝓝 z]
      (fun w => w + c)
  filter_upwards [hn] with w hw
  have hq : (QuotientAddGroup.mk (w + c) : ε.periodTorus) = QuotientAddGroup.mk w := by
    rw [QuotientAddGroup.mk_add, hc, add_zero]
  rw [← hq, ← he]
  exact e.right_inv hw

/-- Local translations are complex smooth. -/
theorem Data.CM.ProjectivePeriodData.periodSection_contDiffAt (e : OpenPartialHomeomorph ε.periodTorus (ε.space))
    (he : ⇑e.symm = (QuotientAddGroup.mk : ε.space → ε.periodTorus))
    (z : ε.space) (hz : QuotientAddGroup.mk z ∈ e.source) :
    ContDiffAt ℂ ∞ (fun w : ε.space => e (QuotientAddGroup.mk w)) z :=
  (contDiffAt_id.add contDiffAt_const).congr_of_eventuallyEq
    (ε.periodSection_eventuallyEq e he z hz)

/-- The compact period quotient carries the complex manifold structure defined by its charts. -/
instance Data.CM.ProjectivePeriodData.periodTorus_isManifold :
    IsManifold (modelWithCornersSelf ℂ (ε.space)) ∞ ε.periodTorus := by
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
theorem Data.CM.ProjectivePeriodData.periodProjection_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ (ε.space))
      (modelWithCornersSelf ℂ (ε.space)) ∞
      (QuotientAddGroup.mk : ε.space → ε.periodTorus) := by
  intro z
  apply contMDiffAt_iff_target.mpr
  refine ⟨QuotientAddGroup.continuous_mk.continuousAt, ?_⟩
  have hs := ε.periodSection_contDiffAt (ε.periodChart (QuotientAddGroup.mk z))
    (ε.periodChart_symm _) z (ε.mem_periodChart_source _)
  simpa only [ε.period_extChart, Function.comp_def] using hs.contMDiffAt

/-- Smoothness of a map out of the quotient can be checked after lifting along the projection. -/
theorem Data.CM.ProjectivePeriodData.contMDiff_of_periodProjection {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {M : Type*} [TopologicalSpace M] [ChartedSpace F M]
    (f : ε.periodTorus → M)
    (hf : ContMDiff (modelWithCornersSelf ℂ (ε.space)) (modelWithCornersSelf ℂ F) ∞
      (fun z : ε.space => f (QuotientAddGroup.mk z))) :
    ContMDiff (modelWithCornersSelf ℂ (ε.space)) (modelWithCornersSelf ℂ F) ∞ f := by
  intro q
  apply contMDiffAt_iff_source.mpr
  simpa only [ε.period_extChart_symm, Function.comp_def] using
    (hf (extChartAt (modelWithCornersSelf ℂ (ε.space)) q q)).contMDiffWithinAt

instance Data.CM.ProjectivePeriodData.periodTorus_contMDiffAdd :
    ContMDiffAdd (modelWithCornersSelf ℂ (ε.space)) ∞ ε.periodTorus where
  contMDiff_add := by
    intro p
    let : ChartedSpace (ε.space × ε.space) (ε.space × ε.space) :=
      chartedSpaceSelf _
    apply contMDiffAt_iff_source.mpr
    have hf : ContMDiff
        (modelWithCornersSelf ℂ (ε.space × ε.space))
        (modelWithCornersSelf ℂ (ε.space)) ∞
        (fun z : ε.space × ε.space =>
          (QuotientAddGroup.mk (z.1 + z.2) : ε.periodTorus)) :=
      ε.periodProjection_contMDiff.comp (contDiff_fst.add contDiff_snd).contMDiff
    simpa only [extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe,
      ε.period_extChart_symm, Function.comp_def, Prod.map_apply, QuotientAddGroup.mk_add] using
      (hf ((extChartAt ((modelWithCornersSelf ℂ (ε.space)).prod
        (modelWithCornersSelf ℂ (ε.space))) p) p)).contMDiffWithinAt

/-- The actual compact complex manifold quotient is a complex Lie group. -/
instance Data.CM.ProjectivePeriodData.periodTorus_lieAddGroup :
    LieAddGroup (modelWithCornersSelf ℂ (ε.space)) ∞ ε.periodTorus where
  contMDiff_neg := by
    apply ε.contMDiff_of_periodProjection
    have hf : ContMDiff (modelWithCornersSelf ℂ (ε.space))
        (modelWithCornersSelf ℂ (ε.space)) ∞
        (fun z : ε.space => (QuotientAddGroup.mk (-z) : ε.periodTorus)) :=
      ε.periodProjection_contMDiff.comp contMDiff_id.neg
    simpa only [QuotientAddGroup.mk_neg] using hf

instance Data.CM.ProjectivePeriodData.periodTorus_connected : ConnectedSpace ε.periodTorus := by
  exact QuotientAddGroup.mk_surjective.connectedSpace QuotientAddGroup.continuous_mk

end

end OAI.RepresentationTheory.Theta.Geometric.Torus
