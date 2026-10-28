import OAI.AlgebraicGeometry.Picard.Homomorphisms.GlobalHomSections
import OAI.AlgebraicGeometry.Picard.Homomorphisms.InternalHomRestriction

/-! # Local Hom Sections -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.LocalHomSections

noncomputable section

/-! Local sections of internal Hom are morphisms of the actual module
sheaves restricted to that open subscheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}} (M N : X.Modules)

def moduleHomOnOpenEquiv (U : X.Opens) :
    (M.restrict U.ι ⟶ N.restrict U.ι) ≃ Γ(InternalHom.Construction.moduleInternalHom M N, U) :=
  (GlobalHomSections.Construction.moduleHomGlobalSectionEquiv (M.restrict U.ι) (N.restrict U.ι)).trans
    ((InternalHomRestriction.Construction.localLinearHomRestrictEquiv U.ι M N ⊤).symm.trans
      (Equiv.cast (congrArg (fun V : X.Opens => (Γ(InternalHom.Construction.moduleInternalHom M N, V) : Type u)) U.ι_image_top)))

theorem moduleHomSection_transport (b : M ⟶ N) (U V : X.Opens) (h : U = V) :
    (Equiv.cast (congrArg (fun W : X.Opens => (Γ(InternalHom.Construction.moduleInternalHom M N, W) : Type u)) h))
      ((InternalHom.Construction.moduleInternalHom M N).presheaf.map U.leTop.op (GlobalHomSections.Construction.moduleHomGlobalSection M N b)) =
      (InternalHom.Construction.moduleInternalHom M N).presheaf.map V.leTop.op (GlobalHomSections.Construction.moduleHomGlobalSection M N b) := by
  cases h
  rfl

theorem moduleHomOnOpenEquiv_restrict (b : M ⟶ N) (U : X.Opens) :
    moduleHomOnOpenEquiv M N U ((Scheme.Modules.restrictFunctor U.ι).map b) =
      (InternalHom.Construction.moduleInternalHom M N).presheaf.map U.leTop.op (GlobalHomSections.Construction.moduleHomGlobalSection M N b) := by
  apply (moduleHomOnOpenEquiv M N U).symm.injective
  rw [Equiv.symm_apply_apply]
  change (Scheme.Modules.restrictFunctor U.ι).map b =
    GlobalHomSections.Construction.moduleHomOfGlobalSection (M.restrict U.ι) (N.restrict U.ι)
      (InternalHomRestriction.Construction.localLinearHomRestrict U.ι M N ⊤
        ((Equiv.cast (congrArg (fun V : X.Opens => (Γ(InternalHom.Construction.moduleInternalHom M N, V) : Type u))
          U.ι_image_top)).symm
            ((InternalHom.Construction.moduleInternalHom M N).presheaf.map U.leTop.op (GlobalHomSections.Construction.moduleHomGlobalSection M N b))))
  have hc : ((Equiv.cast (congrArg (fun W : X.Opens => (Γ(InternalHom.Construction.moduleInternalHom M N, W) : Type u))
      U.ι_image_top)).symm
        ((InternalHom.Construction.moduleInternalHom M N).presheaf.map U.leTop.op (GlobalHomSections.Construction.moduleHomGlobalSection M N b))) =
      (InternalHom.Construction.moduleInternalHom M N).presheaf.map (U.ι ''ᵁ ⊤).leTop.op (GlobalHomSections.Construction.moduleHomGlobalSection M N b) :=
    moduleHomSection_transport M N b U (U.ι ''ᵁ ⊤) U.ι_image_top.symm
  rw [hc]
  apply Scheme.Modules.hom_ext
  intro V
  ext s
  rfl

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.LocalHomSections
