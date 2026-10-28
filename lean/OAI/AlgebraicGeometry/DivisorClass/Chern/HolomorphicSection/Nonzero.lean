import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Data
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OpenExtension

/-! # Nonzero -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Nonzero

noncomputable section

/-! Nonzero original section values are independent of the original local frame and form an open locus. -/

open _root_.TopologicalSpace Set Filter
open scoped _root_.Manifold ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type} [TopologicalSpace M] [ChartedSpace E M]
  (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (s : Data.HolomorphicLineSection u ⊤)

def holomorphicSectionNonzeroAt (x : M) : Prop :=
  s.val x ⟨x, trivial, (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x⟩ ≠ 0

theorem holomorphicSectionNonzeroAt_iff_frame (i x : M)
    (hi : x ∈ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i) :
    holomorphicSectionNonzeroAt u s x ↔ s.val i ⟨x, trivial, hi⟩ ≠ 0 := by
  rw [holomorphicSectionNonzeroAt, s.property i x x trivial hi
    ((Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x)]
  exact mul_ne_zero_iff.trans (and_iff_right (Holomorphic.SlitLog.holomorphicUnit_value_ne_zero
    (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i x) _))

theorem holomorphicSectionNonzeroAt_isOpen : IsOpen {x | holomorphicSectionNonzeroAt u s x} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  let U := (⊤ : Opens M) ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u x
  have hxU : x ∈ U := ⟨trivial, (Holomorphic.CohomologyTransitions.holomorphicCohomologyLocalLifts E M u).mem_domain x⟩
  let f := Holomorphic.OpenExtension.holomorphicOpenExtend (s.val x)
  have hf : ContinuousAt f x := (Holomorphic.OpenExtension.holomorphicOpenExtend_contMDiffOn (s.val x)).continuousOn.continuousAt
    (U.isOpen.mem_nhds hxU)
  have hfx : f x ≠ 0 := fun hz => hx ((Holomorphic.OpenExtension.holomorphicOpenExtend_apply (s.val x) x hxU).symm.trans hz)
  have hfn : ∀ᶠ y in 𝓝 x, f y ≠ 0 := hf (isOpen_compl_singleton.mem_nhds hfx)
  filter_upwards [U.isOpen.mem_nhds hxU, hfn] with y hy hfy
  apply (holomorphicSectionNonzeroAt_iff_frame u s x y hy.2).mpr
  exact (Holomorphic.OpenExtension.holomorphicOpenExtend_apply (s.val x) y hy) ▸ hfy

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.Nonzero
