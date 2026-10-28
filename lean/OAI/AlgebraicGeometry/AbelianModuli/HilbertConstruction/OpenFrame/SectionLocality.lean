import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.DifferenceNaturality
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Section Locality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionLocality

noncomputable section

/-! Compatibility of frame coordinates can be checked on any open cover, by the separatedness of the actual regular-function sheaf. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : Transitions.OpenFrameTransitions U)

theorem openFrameSectionModule_mem_of_locally {V : X.Opens} {α : Type u} (W : α → X.Opens)
    (hW : ∀ a, W a ≤ V) (hcover : V ≤ iSup W) (x : SectionModules.OpenFrameLocalTuple U V)
    (hx : ∀ a, TupleRestrictions.openFrameTupleRestriction U (hW a) x ∈ SectionModules.openFrameSectionModule U D (W a)) :
    x ∈ SectionModules.openFrameSectionModule U D V := by
  simp only [SectionModules.openFrameSectionModule, Submodule.mem_iInf, LinearMap.mem_ker] at hx ⊢
  intro i j
  let Z := (V ⊓ U i) ⊓ U j
  let Q := fun a => (W a ⊓ U i) ⊓ U j
  have hQ (a : α) : Q a ≤ Z := inf_le_inf (inf_le_inf (hW a) (le_refl (U i))) (le_refl (U j))
  have hc : Z ≤ iSup Q := by
    intro z hz
    obtain ⟨a, ha⟩ := Opens.mem_iSup.mp (hcover hz.1.1)
    exact Opens.mem_iSup.mpr ⟨a, ⟨ha, hz.1.2⟩, hz.2⟩
  apply X.sheaf.eq_of_locally_eq' Q Z (fun a => homOfLE (hQ a)) hc
  intro a
  exact (DifferenceNaturality.openFrameDifference_restriction D (hW a) x i j).symm.trans
    ((hx a i j).trans (X.presheaf.map (homOfLE (hQ a)).op).hom.map_zero.symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenFrame.SectionLocality
