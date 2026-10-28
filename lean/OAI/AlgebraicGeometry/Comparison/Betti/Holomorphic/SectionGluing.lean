import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Restrictions

/-! # Section Gluing -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionGluing

noncomputable section

/-! Compatible actual holomorphic vector-valued sections glue uniquely on any open cover. -/

open _root_.TopologicalSpace Filter
open scoped ContDiff _root_.Topology

variable {E F ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem existsUnique_holomorphicSection_glue (V : ι → Opens E)
    (a : ∀ i, CoefficientMem.holomorphicSections (V i) F)
    (hc : ∀ i j (x : E) (hi : x ∈ V i) (hj : x ∈ V j),
      (a i).val ⟨x, hi⟩ = (a j).val ⟨x, hj⟩) :
    ∃! b : CoefficientMem.holomorphicSections (iSup V) F,
      ∀ i (x : V i), b.val ⟨x, le_iSup V i x.property⟩ = (a i).val x := by
  classical
  have hcover (x : ↥(iSup V)) : ∃ i, (x : E) ∈ V i := Opens.mem_iSup.mp x.property
  let g : ↥(iSup V) → F := fun x => (a (hcover x).choose).val ⟨x, (hcover x).choose_spec⟩
  have hg (i : ι) (x : V i) : g ⟨x, le_iSup V i x.property⟩ = (a i).val x := by
    exact hc _ i x _ x.property
  have hgs : ContDiffOn ℂ ∞ (CoefficientMem.openCoefficientExtension (iSup V) g)
      ((iSup V : Opens E) : Set E) := by
    intro x hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    have hs := (a i).property.contDiffAt ((V i).isOpen.mem_nhds hi)
    have heq : CoefficientMem.openCoefficientExtension (iSup V) g =ᶠ[𝓝 x]
        CoefficientMem.openCoefficientExtension (V i) (a i).val := by
      filter_upwards [(V i).isOpen.mem_nhds hi] with y hy
      rw [CoefficientMem.openCoefficientExtension_apply (iSup V) _ ⟨y, le_iSup V i hy⟩,
        CoefficientMem.openCoefficientExtension_apply (V i) _ ⟨y, hy⟩]
      exact hg i ⟨y, hy⟩
    exact (hs.congr_of_eventuallyEq heq).contDiffWithinAt
  refine ⟨⟨g, hgs⟩, hg, ?_⟩
  intro b hb
  apply Subtype.ext
  funext x
  obtain ⟨i, hi⟩ := hcover x
  exact (hb i ⟨x, hi⟩).trans (hg i ⟨x, hi⟩).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SectionGluing
