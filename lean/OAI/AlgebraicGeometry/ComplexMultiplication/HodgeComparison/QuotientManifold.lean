import Mathlib.Topology.Covering.Quotient
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Complex.Basic

/-! # Quotient Manifold -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientManifold.CM.Construction.ComplexLatticeQuotient

noncomputable section

/-! The quotient by a discrete subgroup has its genuine complex
manifold structure, built from local inverses of the quotient projection. -/

open _root_.Topology Filter
open scoped ContDiff _root_.Manifold

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (Λ : AddSubgroup E) [DiscreteTopology Λ]

abbrev Space := E ⧸ Λ

omit [NormedSpace ℂ E] in
theorem projection_isCoveringMap : IsCoveringMap (QuotientAddGroup.mk : E → Space Λ) := by
  apply (Λ.isAddQuotientCoveringMap_of_comm _).isCoveringMap
  exact isDiscrete_iff_discreteTopology.mpr inferInstance

def representative (q : Space Λ) : E := (QuotientAddGroup.mk_surjective q).choose

omit [NormedSpace ℂ E] [DiscreteTopology Λ] in
theorem representative_mk (q : Space Λ) : QuotientAddGroup.mk (representative Λ q) = q :=
  (QuotientAddGroup.mk_surjective q).choose_spec

def quotientChart (q : Space Λ) : OpenPartialHomeomorph (Space Λ) E :=
  (projection_isCoveringMap Λ).isLocalHomeomorph.localInverseAt (representative Λ q)

omit [NormedSpace ℂ E] in
theorem quotientChart_symm (q : Space Λ) :
    ⇑(quotientChart Λ q).symm = (QuotientAddGroup.mk : E → Space Λ) :=
  (projection_isCoveringMap Λ).isLocalHomeomorph.localInverseAt_symm _

omit [NormedSpace ℂ E] in
theorem mem_quotientChart_source (q : Space Λ) : q ∈ (quotientChart Λ q).source := by
  have h := (projection_isCoveringMap Λ).isLocalHomeomorph.apply_self_mem_localInverseAt_source
    (x := representative Λ q)
  simpa only [quotientChart, representative_mk] using h

scoped instance quotient_chartedSpace : ChartedSpace E (Space Λ) where
  atlas := Set.range (quotientChart Λ)
  chartAt := quotientChart Λ
  mem_chart_source := mem_quotientChart_source Λ
  chart_mem_atlas q := ⟨q, rfl⟩

theorem quotient_extChart (q : Space Λ) :
    ⇑(extChartAt 𝓘(ℂ, E) q) = quotientChart Λ q := rfl

theorem quotient_extChart_symm (q : Space Λ) :
    ⇑(extChartAt 𝓘(ℂ, E) q).symm = (QuotientAddGroup.mk : E → Space Λ) :=
  quotientChart_symm Λ q

omit [NormedSpace ℂ E] [DiscreteTopology Λ] in
theorem quotientSection_eventuallyEq (e : OpenPartialHomeomorph (Space Λ) E)
    (he : ⇑e.symm = (QuotientAddGroup.mk : E → Space Λ))
    (z : E) (hz : QuotientAddGroup.mk z ∈ e.source) :
    (fun w : E => e (QuotientAddGroup.mk w)) =ᶠ[𝓝 z]
      (fun w => w + (e (QuotientAddGroup.mk z) - z)) := by
  let c : E := e (QuotientAddGroup.mk z) - z
  have hc : (QuotientAddGroup.mk c : Space Λ) = 0 := by
    change (QuotientAddGroup.mk (e (QuotientAddGroup.mk z) - z) : Space Λ) = 0
    have hq := e.left_inv hz
    rw [he] at hq
    rw [QuotientAddGroup.mk_sub, hq, sub_self]
  have hn : ∀ᶠ w in 𝓝 z, w + c ∈ e.target := by
    apply (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds
    apply e.open_target.mem_nhds
    change z + c ∈ e.target
    simpa [c, add_comm] using e.map_source hz
  change (fun w : E => e (QuotientAddGroup.mk w)) =ᶠ[𝓝 z] (fun w => w + c)
  filter_upwards [hn] with w hw
  have hq : (QuotientAddGroup.mk (w + c) : Space Λ) = QuotientAddGroup.mk w := by
    rw [QuotientAddGroup.mk_add, hc, add_zero]
  rw [← hq, ← he]
  exact e.right_inv hw

omit [DiscreteTopology Λ] in
theorem quotientSection_contDiffAt (e : OpenPartialHomeomorph (Space Λ) E)
    (he : ⇑e.symm = (QuotientAddGroup.mk : E → Space Λ))
    (z : E) (hz : QuotientAddGroup.mk z ∈ e.source) :
    ContDiffAt ℂ ∞ (fun w : E => e (QuotientAddGroup.mk w)) z :=
  (contDiffAt_id.add contDiffAt_const).congr_of_eventuallyEq
    (quotientSection_eventuallyEq Λ e he z hz)

scoped instance quotient_isManifold : IsManifold 𝓘(ℂ, E) ∞ (Space Λ) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨q, rfl⟩ := he
  obtain ⟨q', rfl⟩ := he'
  intro z hz
  have hz' : QuotientAddGroup.mk z ∈ (quotientChart Λ q').source := by
    have ht : (quotientChart Λ q).symm z ∈ (quotientChart Λ q').source := hz.1.2
    simpa only [quotientChart_symm] using ht
  have hs := quotientSection_contDiffAt Λ (quotientChart Λ q') (quotientChart_symm Λ q') z hz'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_def,
    OpenPartialHomeomorph.coe_trans, quotientChart_symm, id_eq] using hs.contDiffWithinAt

theorem projection_contMDiff :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞ (QuotientAddGroup.mk : E → Space Λ) := by
  intro z
  apply contMDiffAt_iff_target.mpr
  refine ⟨QuotientAddGroup.continuous_mk.continuousAt, ?_⟩
  have hs := quotientSection_contDiffAt Λ (quotientChart Λ (QuotientAddGroup.mk z))
    (quotientChart_symm Λ _) z (mem_quotientChart_source Λ _)
  simpa only [quotient_extChart, Function.comp_def] using hs.contMDiffAt

theorem contMDiff_of_projection {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {M : Type*} [TopologicalSpace M] [ChartedSpace F M]
    (f : Space Λ → M)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ (fun z : E => f (QuotientAddGroup.mk z))) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, F) ∞ f := by
  intro q
  apply contMDiffAt_iff_source.mpr
  simpa only [quotient_extChart_symm, Function.comp_def] using
    (hf (extChartAt 𝓘(ℂ, E) q q)).contMDiffWithinAt

scoped instance quotient_contMDiffAdd : ContMDiffAdd 𝓘(ℂ, E) ∞ (Space Λ) where
  contMDiff_add := by
    intro p
    let : ChartedSpace (E × E) (E × E) := chartedSpaceSelf _
    apply contMDiffAt_iff_source.mpr
    have hf : ContMDiff 𝓘(ℂ, E × E) 𝓘(ℂ, E) ∞
        (fun z : E × E => (QuotientAddGroup.mk (z.1 + z.2) : Space Λ)) :=
      (projection_contMDiff Λ).comp (contDiff_fst.add contDiff_snd).contMDiff
    simpa only [extChartAt_prod, PartialEquiv.prod_symm, PartialEquiv.prod_coe,
      quotient_extChart_symm, Function.comp_def, Prod.map_apply, QuotientAddGroup.mk_add] using
      (hf (extChartAt (𝓘(ℂ, E).prod 𝓘(ℂ, E)) p p)).contMDiffWithinAt

scoped instance quotient_lieAddGroup : LieAddGroup 𝓘(ℂ, E) ∞ (Space Λ) where
  contMDiff_neg := by
    apply contMDiff_of_projection Λ
    have hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ∞
        (fun z : E => (QuotientAddGroup.mk (-z) : Space Λ)) :=
      (projection_contMDiff Λ).comp contMDiff_id.neg
    simpa only [QuotientAddGroup.mk_neg] using hf

scoped instance quotient_connected : ConnectedSpace (Space Λ) :=
  QuotientAddGroup.mk_surjective.connectedSpace QuotientAddGroup.continuous_mk

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientManifold.CM.Construction.ComplexLatticeQuotient
