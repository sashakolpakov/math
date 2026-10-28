import OAI.AlgebraicGeometry.Picard.Homomorphisms.ModuleHomGluing

/-! # Pullback Hom Gluing -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.PullbackHomGluing

noncomputable section

/-! The local Hom section and gluing correspondence, expressed in the
canonical pullbacks to open subschemes used by the descent construction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u v

variable {X : Scheme.{u}} (M N : X.Modules)

def pullbackHomToRestrictedEquiv (U : X.Opens) :
    ((Scheme.Modules.pullback U.ι).obj M ⟶ (Scheme.Modules.pullback U.ι).obj N) ≃
      (M.restrict U.ι ⟶ N.restrict U.ι) :=
  Iso.homCongr ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app N).symm

theorem pullbackHomToRestrictedEquiv_map (U : X.Opens) (b : M ⟶ N) :
    pullbackHomToRestrictedEquiv M N U ((Scheme.Modules.pullback U.ι).map b) =
      (Scheme.Modules.restrictFunctor U.ι).map b :=
  NatIso.naturality_2 (Scheme.Modules.restrictFunctorIsoPullback U.ι) b

def pullbackHomOnOpenEquiv (U : X.Opens) :
    ((Scheme.Modules.pullback U.ι).obj M ⟶ (Scheme.Modules.pullback U.ι).obj N) ≃
      Γ(InternalHom.Construction.moduleInternalHom M N, U) :=
  (pullbackHomToRestrictedEquiv M N U).trans (LocalHomSections.Construction.moduleHomOnOpenEquiv M N U)

theorem pullbackHomOnOpenEquiv_map (U : X.Opens) (b : M ⟶ N) :
    pullbackHomOnOpenEquiv M N U ((Scheme.Modules.pullback U.ι).map b) =
      (InternalHom.Construction.moduleInternalHom M N).presheaf.map U.leTop.op (GlobalHomSections.Construction.moduleHomGlobalSection M N b) :=
  (congrArg (LocalHomSections.Construction.moduleHomOnOpenEquiv M N U) (pullbackHomToRestrictedEquiv_map M N U b)).trans
    (LocalHomSections.Construction.moduleHomOnOpenEquiv_restrict M N b U)

theorem pullbackModuleHom_glue {ι : Type v} (U : ι → X.Opens)
    (hU : ∀ x : X, ∃ i, x ∈ U i)
    (b : ∀ i, (Scheme.Modules.pullback (U i).ι).obj M ⟶ (Scheme.Modules.pullback (U i).ι).obj N)
    (hb : ∀ i j,
      (InternalHom.Construction.moduleInternalHom M N).presheaf.map
          (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op
          (pullbackHomOnOpenEquiv M N (U i) (b i)) =
        (InternalHom.Construction.moduleInternalHom M N).presheaf.map
          (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op
          (pullbackHomOnOpenEquiv M N (U j) (b j))) :
    ∃! a : M ⟶ N, ∀ i, (Scheme.Modules.pullback (U i).ι).map a = b i := by
  obtain ⟨a, ha, huniq⟩ := ModuleHomGluing.Construction.moduleHom_glue M N U hU
    (fun i => pullbackHomToRestrictedEquiv M N (U i) (b i)) hb
  have hap : ∀ i, (Scheme.Modules.pullback (U i).ι).map a = b i := by
    intro i
    apply (pullbackHomToRestrictedEquiv M N (U i)).injective
    exact (pullbackHomToRestrictedEquiv_map M N (U i) a).trans (ha i)
  refine ⟨a, hap, ?_⟩
  intro a' ha'
  apply huniq
  intro i
  exact (pullbackHomToRestrictedEquiv_map M N (U i) a').symm.trans
    (congrArg (pullbackHomToRestrictedEquiv M N (U i)) (ha' i))

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.PullbackHomGluing
