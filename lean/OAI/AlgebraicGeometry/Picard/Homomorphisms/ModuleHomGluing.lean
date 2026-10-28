import OAI.AlgebraicGeometry.Picard.Homomorphisms.LocalHomSections
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Module Hom Gluing -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomGluing

noncomputable section

/-! Compatible local morphisms of module sheaves glue uniquely. The
compatibility is the usual restriction of their internal-Hom sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u v

variable {X : Scheme.{u}} (M N : X.Modules)

theorem moduleHom_glue {ι : Type v} (U : ι → X.Opens)
    (hU : ∀ x : X, ∃ i, x ∈ U i)
    (b : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι)
    (hb : ∀ i j,
      (InternalHom.Construction.moduleInternalHom M N).presheaf.map
          (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op
          (LocalHomSections.Construction.moduleHomOnOpenEquiv M N (U i) (b i)) =
        (InternalHom.Construction.moduleInternalHom M N).presheaf.map
          (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op
          (LocalHomSections.Construction.moduleHomOnOpenEquiv M N (U j) (b j))) :
    ∃! a : M ⟶ N, ∀ i, (Scheme.Modules.restrictFunctor (U i).ι).map a = b i := by
  let H := InternalHom.Construction.moduleInternalHom M N
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨H.presheaf, H.isSheaf⟩
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    exact Opens.mem_iSup.mpr (hU x)
  obtain ⟨z, hz, huniq⟩ := F.existsUnique_gluing' U ⊤ (fun i => (U i).leTop) hcover
    (fun i => LocalHomSections.Construction.moduleHomOnOpenEquiv M N (U i) (b i)) hb
  let a := (GlobalHomSections.Construction.moduleHomGlobalSectionEquiv M N).symm z
  have ha : ∀ i, (Scheme.Modules.restrictFunctor (U i).ι).map a = b i := by
    intro i
    apply (LocalHomSections.Construction.moduleHomOnOpenEquiv M N (U i)).injective
    rw [LocalHomSections.Construction.moduleHomOnOpenEquiv_restrict]
    exact (congrArg (fun t => H.presheaf.map (U i).leTop.op t)
      ((GlobalHomSections.Construction.moduleHomGlobalSectionEquiv M N).apply_symm_apply z)).trans (hz i)
  refine ⟨a, ha, ?_⟩
  intro a' ha'
  apply (GlobalHomSections.Construction.moduleHomGlobalSectionEquiv M N).injective
  change GlobalHomSections.Construction.moduleHomGlobalSection M N a' = (GlobalHomSections.Construction.moduleHomGlobalSectionEquiv M N) a
  rw [show (GlobalHomSections.Construction.moduleHomGlobalSectionEquiv M N) a = z from
    (GlobalHomSections.Construction.moduleHomGlobalSectionEquiv M N).apply_symm_apply z]
  apply huniq
  intro i
  exact (LocalHomSections.Construction.moduleHomOnOpenEquiv_restrict M N a' (U i)).symm.trans
    (congrArg (LocalHomSections.Construction.moduleHomOnOpenEquiv M N (U i)) (ha' i))

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomGluing
