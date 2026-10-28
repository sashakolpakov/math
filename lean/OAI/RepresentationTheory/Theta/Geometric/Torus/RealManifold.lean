import OAI.RepresentationTheory.Theta.Geometric.Torus.Manifold
import OAI.Analysis.DifferentialForms.Manifold.Derivative

/-! # Real Manifold -/

namespace OAI.RepresentationTheory.Theta.Geometric.Torus

noncomputable section

/-!
# Real tangent coordinates on the generic projective torus

The existing complex atlas also defines a real smooth manifold. Its chart
transitions are locally translations and have identity real derivative.
Thus their maps out of the actual tangent space agree on every overlap.
-/

open scoped Classical _root_.NumberField ContDiff _root_.Manifold
open _root_.Topology Filter

open _root_.NumberField

variable (ε : Data.CM.ProjectivePeriodData)

theorem Data.CM.ProjectivePeriodData.periodSection_realContDiffAt
    (e : OpenPartialHomeomorph ε.periodTorus (ε.space))
    (he : ⇑e.symm = (QuotientAddGroup.mk : ε.space → ε.periodTorus))
    (z : ε.space) (hz : QuotientAddGroup.mk z ∈ e.source) :
    ContDiffAt ℝ ∞ (fun w : ε.space => e (QuotientAddGroup.mk w)) z :=
  (contDiffAt_id.add contDiffAt_const).congr_of_eventuallyEq
    (ε.periodSection_eventuallyEq e he z hz)

/-- The real manifold uses exactly the atlas of the complex period torus. -/
instance Data.CM.ProjectivePeriodData.periodTorus_realIsManifold : IsManifold 𝓘(ℝ, ε.space) ∞ ε.periodTorus := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨q, rfl⟩ := he
  obtain ⟨q', rfl⟩ := he'
  intro z hz
  have hz' : QuotientAddGroup.mk z ∈ (ε.periodChart q').source := by
    have ht : (ε.periodChart q).symm z ∈ (ε.periodChart q').source := hz.1.2
    simpa only [ε.periodChart_symm] using ht
  have hs := ε.periodSection_realContDiffAt (ε.periodChart q') (ε.periodChart_symm q') z hz'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_def,
    OpenPartialHomeomorph.coe_trans, ε.periodChart_symm, id_eq] using hs.contDiffWithinAt

/-- The derivative is that of the actual local section composed with the projection. -/
theorem Data.CM.ProjectivePeriodData.periodSection_hasFDerivAt
    (e : OpenPartialHomeomorph ε.periodTorus (ε.space))
    (he : ⇑e.symm = (QuotientAddGroup.mk : ε.space → ε.periodTorus))
    (z : ε.space) (hz : QuotientAddGroup.mk z ∈ e.source) :
    HasFDerivAt (fun w : ε.space => e (QuotientAddGroup.mk w))
      (ContinuousLinearMap.id ℝ (ε.space)) z :=
  ((hasFDerivAt_id z).add_const (e (QuotientAddGroup.mk z) - z)).congr_of_eventuallyEq
    (ε.periodSection_eventuallyEq e he z hz)

theorem Data.CM.ProjectivePeriodData.periodChart_mem_atlas (q : ε.periodTorus) :
    ε.periodChart q ∈ atlas (ε.space) ε.periodTorus := ⟨q, rfl⟩

/-- Derivatives of the real coordinate changes are identity maps. -/
theorem Data.CM.ProjectivePeriodData.periodChart_transition_fderiv (i j : ε.periodTorus) (z : ε.space)
    (hz : (ε.periodChart i).symm z ∈ (ε.periodChart j).source) :
    fderiv ℝ (ε.periodChart j ∘ (ε.periodChart i).symm) z =
      ContinuousLinearMap.id ℝ (ε.space) := by
  rw [ε.periodChart_symm] at hz ⊢
  exact (ε.periodSection_hasFDerivAt (ε.periodChart j) (ε.periodChart_symm j) z hz).fderiv

/-- Charts give the same real-linear coordinates on an actual tangent fiber. -/
theorem Data.CM.ProjectivePeriodData.periodChart_tangentMap_eq (i j q : ε.periodTorus)
    (hi : q ∈ (ε.periodChart i).source) (hj : q ∈ (ε.periodChart j).source) :
    Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (ε.periodChart i) q = Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (ε.periodChart j) q := by
  have h := Analysis.DifferentialForms.Manifold.Derivative.chartTangentMap_transition_comp (ε.periodChart i) (ε.periodChart j)
    (ε.periodChart_mem_atlas i) (ε.periodChart_mem_atlas j) hi hj
  rw [ε.periodChart_transition_fderiv i j _
    (by simpa only [(ε.periodChart i).left_inv hi] using hj)] at h
  simpa only [ContinuousLinearMap.id_comp] using h

end

end OAI.RepresentationTheory.Theta.Geometric.Torus
