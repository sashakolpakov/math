import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing

noncomputable section

/-! Glue compatible local module sections into actual global sheaf morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

universe u v

variable {X : Scheme.{u}} (M : X.Modules)

/-- Restricting the global value of a section map gives its local value. -/
theorem moduleSectionHomEquiv_restrict (s : Line.Bundles.structureModule X ⟶ M) (U : X.Opens) :
    M.presheaf.map U.leTop.op (Global.Sections.moduleSectionHomEquiv M s) = s.app U (1 : Γ(X, U)) :=
  (M.unitHomEquiv s).property U.leTop.op

/-- Compatible sections on an open cover determine a unique morphism from the
structure module. No choice of local frames enters the gluing result. -/
theorem moduleSection_glue {ι : Type v} (U : ι → X.Opens)
    (hU : ∀ x : X, ∃ i, x ∈ U i) (s : ∀ i, Γ(M, U i))
    (hs : ∀ i j,
      M.presheaf.map (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op (s i) =
      M.presheaf.map (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op (s j)) :
    ∃! t : Line.Bundles.structureModule X ⟶ M, ∀ i, t.app (U i) (1 : Γ(X, U i)) = s i := by
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf, M.isSheaf⟩
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    exact Opens.mem_iSup.mpr (hU x)
  obtain ⟨z, hz, huniq⟩ := F.existsUnique_gluing' U ⊤ (fun i => (U i).leTop) hcover s hs
  refine ⟨(Global.Sections.moduleSectionHomEquiv M).symm z, fun i => ?_, fun t ht => ?_⟩
  · exact (moduleSectionHomEquiv_restrict M ((Global.Sections.moduleSectionHomEquiv M).symm z) (U i)).symm.trans
      ((congrArg (fun a => M.presheaf.map (U i).leTop.op a)
        ((Global.Sections.moduleSectionHomEquiv M).apply_symm_apply z)).trans (hz i))
  · apply (Global.Sections.moduleSectionHomEquiv M).injective
    rw [Equiv.apply_symm_apply]
    apply huniq
    intro i
    exact (moduleSectionHomEquiv_restrict M t (U i)).trans (ht i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing
