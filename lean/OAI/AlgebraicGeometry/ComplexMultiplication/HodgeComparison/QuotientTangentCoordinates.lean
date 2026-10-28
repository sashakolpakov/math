import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientManifold
import OAI.Analysis.DifferentialForms.Manifold.Derivative

/-! # Quotient Tangent Coordinates -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient

noncomputable section

/-! The quotient charts have identity real transition derivatives.
Their maps from each actual tangent fiber therefore agree. -/

open _root_.Topology Filter
open scoped ContDiff _root_.Manifold
open scoped OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientManifold.CM.Construction.ComplexLatticeQuotient

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (Λ : AddSubgroup E) [DiscreteTopology Λ]

omit [DiscreteTopology Λ] in
theorem quotientSection_realContDiffAt (e : OpenPartialHomeomorph (QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) E)
    (he : ⇑e.symm = (QuotientAddGroup.mk : E → QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ))
    (z : E) (hz : QuotientAddGroup.mk z ∈ e.source) :
    ContDiffAt ℝ ∞ (fun w : E => e (QuotientAddGroup.mk w)) z :=
  (contDiffAt_id.add contDiffAt_const).congr_of_eventuallyEq
    (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientSection_eventuallyEq Λ e he z hz)

scoped instance quotient_realIsManifold : IsManifold 𝓘(ℝ, E) ∞ (QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) := by
  apply isManifold_of_contDiffOn
  intro e e' he he'
  obtain ⟨q, rfl⟩ := he
  obtain ⟨q', rfl⟩ := he'
  intro z hz
  have hz' : QuotientAddGroup.mk z ∈ (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ q').source := by
    have ht : (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ q).symm z ∈ (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ q').source := hz.1.2
    simpa only [QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart_symm] using ht
  have hs := quotientSection_realContDiffAt Λ (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ q') (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart_symm Λ q') z hz'
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_def,
    OpenPartialHomeomorph.coe_trans, QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart_symm, id_eq] using hs.contDiffWithinAt

omit [DiscreteTopology Λ] in
theorem quotientSection_hasFDerivAt (e : OpenPartialHomeomorph (QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) E)
    (he : ⇑e.symm = (QuotientAddGroup.mk : E → QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ))
    (z : E) (hz : QuotientAddGroup.mk z ∈ e.source) :
    HasFDerivAt (fun w : E => e (QuotientAddGroup.mk w)) (ContinuousLinearMap.id ℝ E) z :=
  ((hasFDerivAt_id z).add_const (e (QuotientAddGroup.mk z) - z)).congr_of_eventuallyEq
    (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientSection_eventuallyEq Λ e he z hz)

omit [NormedSpace ℝ E] in
theorem quotientChart_mem_atlas (q : QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) : QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ q ∈ atlas E (QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) := ⟨q, rfl⟩

theorem quotientChart_transition_fderiv (i j : QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) (z : E)
    (hz : (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ i).symm z ∈ (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ j).source) :
    fderiv ℝ (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ j ∘ (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ i).symm) z = ContinuousLinearMap.id ℝ E := by
  rw [QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart_symm] at hz ⊢
  exact (quotientSection_hasFDerivAt Λ (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ j) (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart_symm Λ j) z hz).fderiv

theorem quotientChart_tangentMap_eq (i j q : QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ)
    (hi : q ∈ (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ i).source) (hj : q ∈ (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ j).source) :
    Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ i) q = Analysis.DifferentialForms.Manifold.Charts.chartTangentMap (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ j) q := by
  have h := Analysis.DifferentialForms.Manifold.Derivative.chartTangentMap_transition_comp (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ i) (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ j)
    (quotientChart_mem_atlas Λ i) (quotientChart_mem_atlas Λ j) hi hj
  rw [quotientChart_transition_fderiv Λ i j _
    (by simpa only [(QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ i).left_inv hi] using hj)] at h
  simpa only [ContinuousLinearMap.id_comp] using h

theorem quotient_real_extChart (q : QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) :
    ⇑(extChartAt 𝓘(ℝ, E) q) = QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ q := rfl

theorem projection_realContMDiff :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (QuotientAddGroup.mk : E → QuotientManifold.CM.Construction.ComplexLatticeQuotient.Space Λ) := by
  intro z
  apply contMDiffAt_iff_target.mpr
  refine ⟨QuotientAddGroup.continuous_mk.continuousAt, ?_⟩
  have hs := quotientSection_realContDiffAt Λ (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart Λ (QuotientAddGroup.mk z))
    (QuotientManifold.CM.Construction.ComplexLatticeQuotient.quotientChart_symm Λ _) z (QuotientManifold.CM.Construction.ComplexLatticeQuotient.mem_quotientChart_source Λ _)
  simpa only [quotient_real_extChart, Function.comp_def] using hs.contMDiffAt

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.QuotientTangentCoordinates.CM.Construction.ComplexLatticeQuotient
