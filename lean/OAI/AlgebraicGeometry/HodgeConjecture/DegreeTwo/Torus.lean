import Mathlib.Topology.Covering.Quotient
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting

/-! # Torus -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient

noncomputable section

/-!
# DegreeTwo: analytic charts for a discrete lattice quotient

The construction generalizes the actual quotient-chart argument in
Hodge.CM.CMPeriodTorus from CM period spaces to every complex normed
space with a discrete additive lattice. It makes BettiLattice's local-lift notion
compatible with manifold differentiability. It does not assume a
uniformization of an abelian variety.
-/

open _root_.Topology Filter
open scoped _root_.Manifold ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  (Λ : Submodule ℤ V) [DiscreteTopology Λ]

abbrev Point := V ⧸ Λ.toAddSubgroup

omit [NormedSpace ℂ V] in
/-- Discreteness makes the lattice projection a covering map. -/
theorem projection_isCoveringMap :
    IsCoveringMap (QuotientAddGroup.mk : V → Point Λ) := by
  apply (Λ.toAddSubgroup.isAddQuotientCoveringMap_of_comm _).isCoveringMap
  exact SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance

/-- A representative used only to choose a local chart at each quotient point. -/
def representative (q : Point Λ) : V :=
  (QuotientAddGroup.mk_surjective q).choose

omit [NormedSpace ℂ V] [DiscreteTopology Λ] in
theorem representative_mk (q : Point Λ) :
    QuotientAddGroup.mk (representative Λ q) = q :=
  (QuotientAddGroup.mk_surjective q).choose_spec

/-- A local inverse of the lattice projection. -/
def chart (q : Point Λ) : OpenPartialHomeomorph (Point Λ) V :=
  (projection_isCoveringMap Λ).isLocalHomeomorph.localInverseAt (representative Λ q)

omit [NormedSpace ℂ V] in
theorem chart_symm (q : Point Λ) :
    ⇑(chart Λ q).symm = (QuotientAddGroup.mk : V → Point Λ) :=
  (projection_isCoveringMap Λ).isLocalHomeomorph.localInverseAt_symm _

omit [NormedSpace ℂ V] in
theorem mem_chart_source (q : Point Λ) : q ∈ (chart Λ q).source := by
  have h := (projection_isCoveringMap Λ).isLocalHomeomorph.apply_self_mem_localInverseAt_source
    (x := representative Λ q)
  simpa only [chart, representative_mk Λ] using h

instance quotient_chartedSpace : ChartedSpace V (Point Λ) where
  atlas := Set.range (chart Λ)
  chartAt := chart Λ
  mem_chart_source := LatticeQuotient.mem_chart_source Λ
  chart_mem_atlas q := ⟨q, rfl⟩

theorem extChart (q : Point Λ) :
    ⇑(extChartAt (modelWithCornersSelf ℂ V) q) = chart Λ q := rfl

theorem extChart_symm (q : Point Λ) :
    ⇑(extChartAt (modelWithCornersSelf ℂ V) q).symm =
      (QuotientAddGroup.mk : V → Point Λ) := by
  change ⇑(chart Λ q).symm = _
  exact chart_symm Λ q

omit [NormedSpace ℂ V] [DiscreteTopology Λ] in
/-- Every local inverse of the projection is locally a translation after precomposition
with the projection. -/
theorem section_eventuallyEq (e : OpenPartialHomeomorph (Point Λ) V)
    (he : ⇑e.symm = (QuotientAddGroup.mk : V → Point Λ))
    (z : V) (hz : QuotientAddGroup.mk z ∈ e.source) :
    (fun w : V => e (QuotientAddGroup.mk w)) =ᶠ[𝓝 z]
      (fun w => w + (e (QuotientAddGroup.mk z) - z)) := by
  let c : V := e (QuotientAddGroup.mk z) - z
  have hc : (QuotientAddGroup.mk c : Point Λ) = 0 := by
    change (QuotientAddGroup.mk (e (QuotientAddGroup.mk z) - z) : Point Λ) = 0
    have hq := e.left_inv hz
    rw [he] at hq
    rw [QuotientAddGroup.mk_sub, hq, sub_self]
  have hn : ∀ᶠ w in 𝓝 z, w + c ∈ e.target := by
    apply (continuous_id.add continuous_const).continuousAt.preimage_mem_nhds
    apply e.open_target.mem_nhds
    change z + c ∈ e.target
    simpa [c, add_comm] using e.map_source hz
  change (fun w : V => e (QuotientAddGroup.mk w)) =ᶠ[𝓝 z]
      (fun w => w + c)
  filter_upwards [hn] with w hw
  have hq : (QuotientAddGroup.mk (w + c) : Point Λ) = QuotientAddGroup.mk w := by
    rw [QuotientAddGroup.mk_add, hc, add_zero]
  rw [← hq, ← he]
  exact e.right_inv hw

omit [DiscreteTopology Λ] in
/-- Local translations are complex smooth. -/
theorem section_contDiffAt (e : OpenPartialHomeomorph (Point Λ) V)
    (he : ⇑e.symm = (QuotientAddGroup.mk : V → Point Λ))
    (z : V) (hz : QuotientAddGroup.mk z ∈ e.source) :
    ContDiffAt ℂ ∞ (fun w : V => e (QuotientAddGroup.mk w)) z :=
  (contDiffAt_id.add contDiffAt_const).congr_of_eventuallyEq
    (section_eventuallyEq Λ e he z hz)

/-- The discrete lattice quotient carries the complex manifold structure defined by its charts. -/
instance quotient_isManifold :
    IsManifold (modelWithCornersSelf ℂ V) ∞ (Point Λ) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨q, rfl⟩ := he
  obtain ⟨q', rfl⟩ := he'
  intro z hz
  have hz' : QuotientAddGroup.mk z ∈ (chart Λ q').source := by
    have ht : (chart Λ q).symm z ∈ (chart Λ q').source := hz.1.2
    simpa only [chart_symm Λ] using ht
  have hs := section_contDiffAt Λ (chart Λ q') (chart_symm Λ q') z hz'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_def,
    OpenPartialHomeomorph.coe_trans, chart_symm Λ, id_eq] using hs.contDiffWithinAt

/-- The covering projection is complex smooth for the constructed manifold structure. -/
theorem projection_contMDiff :
    ContMDiff (modelWithCornersSelf ℂ V)
      (modelWithCornersSelf ℂ V) ∞
      (QuotientAddGroup.mk : V → Point Λ) := by
  intro z
  apply contMDiffAt_iff_target.mpr
  refine ⟨QuotientAddGroup.continuous_mk.continuousAt, ?_⟩
  have hs := section_contDiffAt Λ (chart Λ (QuotientAddGroup.mk z))
    (chart_symm Λ _) z (LatticeQuotient.mem_chart_source Λ _)
  simpa only [extChart Λ, Function.comp_def] using hs.contMDiffAt

/-- Differentiability out of the quotient can be checked on its covering space. -/
theorem mdifferentiable_of_projection
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {M : Type*} [TopologicalSpace M] [ChartedSpace F M]
    (f : Point Λ → M)
    (hf : MDifferentiable (𝓘(ℂ, V)) (𝓘(ℂ, F))
      (fun z : V => f (QuotientAddGroup.mk z))) :
    MDifferentiable (𝓘(ℂ, V)) (𝓘(ℂ, F)) f := by
  intro q
  apply (mdifferentiableAt_iff_source_of_mem_source (LatticeQuotient.mem_chart_source Λ q)).mpr
  simpa only [extChart_symm, Function.comp_def, modelWithCornersSelf_coe,
    Set.range_id] using
    (hf (extChartAt (𝓘(ℂ, V)) q q)).mdifferentiableWithinAt

/-- BettiLattice's local holomorphic lifts give differentiability for the actual
quotient manifold structures. No global lift is assumed. -/
theorem mdifferentiable_of_local_lifts
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (Γ : Submodule ℤ W) [DiscreteTopology Γ]
    (g : Point Λ → Point Γ)
    (hg : ∀ v : V, ∃ (s : Set V) (F : V → W),
      IsOpen s ∧ v ∈ s ∧ DifferentiableOn ℂ F s ∧
      ∀ w ∈ s, g (QuotientAddGroup.mk w) = QuotientAddGroup.mk (F w)) :
    MDifferentiable (𝓘(ℂ, V)) (𝓘(ℂ, W)) g := by
  apply mdifferentiable_of_projection Λ
  intro v
  obtain ⟨s, F, hs, hv, hF, hFg⟩ := hg v
  have hd := (hF v hv).differentiableAt (hs.mem_nhds hv)
  have hp := ((projection_contMDiff Γ).mdifferentiable (by simp)) (F v)
  apply (hp.comp v hd.mdifferentiableAt).congr_of_eventuallyEq
  filter_upwards [hs.mem_nhds hv] with w hw
  exact hFg w hw

/-- The actual fundamental group is the deck-transformation lattice;
the opposite group records the path-composition convention. -/
def fundamentalGroupEquiv :
    FundamentalGroup (Point Λ) (0 : Point Λ) ≃* (Multiplicative Λ)ᵐᵒᵖ :=
  (Λ.toAddSubgroup.isAddQuotientCoveringMap_of_comm
    (SetLike.isDiscrete_iff_discreteTopology.mpr inferInstance)).fundamentalGroupEquiv
      ⟨0, rfl⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Torus.Constructions.LatticeQuotient
