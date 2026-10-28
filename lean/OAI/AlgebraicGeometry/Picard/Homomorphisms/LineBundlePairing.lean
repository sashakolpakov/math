import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleDual
import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleEpi

/-! # Line Bundle Pairing -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundlePairing

noncomputable section

/-! Local dual frames for the evaluation pairing of a line bundle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X Y : Scheme.{u}}

def internalHomOfHom {M N : X.Modules} (f : M ⟶ N) (U : X.Opens) :
    Γ(InternalHom.Construction.moduleInternalHom M N, U) :=
  ⟨Functor.whiskerLeft (Over.forget U).op f.mapPresheaf,
    fun _V r s => f.app_smul r s⟩

theorem internalHomRestrict_eval (f : X ⟶ Y) [IsOpenImmersion f] (M N : Y.Modules)
    (U : X.Opens) (a : Γ(InternalHom.Construction.moduleInternalHom M N, f ''ᵁ U)) (s : Γ(M, f ''ᵁ U)) :
    TensorHom.Construction.internalHomEval (M.restrict f) (N.restrict f) U (InternalHomRestriction.Construction.localLinearHomRestrict f M N U a) s =
      TensorHom.Construction.internalHomEval M N (f ''ᵁ U) a s := rfl

theorem dual_sections_of_frame (f : X ⟶ Y) [IsOpenImmersion f]
    (L : Y.Modules) (e : L.restrict f ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (U : X.Opens) :
    ∃ (a : Γ(InternalHom.Construction.moduleInternalHom L (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y), f ''ᵁ U))
      (s : Γ(L, f ''ᵁ U)),
      TensorHom.Construction.internalHomEval L (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) (f ''ᵁ U) a s = (1 : Γ(Y, f ''ᵁ U)) := by
  let q := Scheme.Modules.restrictUnitIso f
  let b := internalHomOfHom (e.hom ≫ q.inv) U
  let a := (InternalHomRestriction.Construction.localLinearHomRestrictEquiv f L (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) U).symm b
  let s : Γ(L, f ''ᵁ U) := e.inv.app U (1 : Γ(X, U))
  refine ⟨a, s, ?_⟩
  rw [← internalHomRestrict_eval f L (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) U a s]
  have ha : InternalHomRestriction.Construction.localLinearHomRestrict f L (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) U a = b :=
    (InternalHomRestriction.Construction.localLinearHomRestrictEquiv f L (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule Y) U).apply_symm_apply b
  rw [ha]
  change (e.inv ≫ e.hom ≫ q.inv).app U (1 : Γ(X, U)) = (1 : Γ(Y, f ''ᵁ U))
  rw [e.inv_hom_id_assoc]
  change (f.appIso U).inv (1 : Γ(X, U)) = (1 : Γ(Y, f ''ᵁ U))
  exact (f.appIso U).inv.hom.map_one

theorem lineBundle_dual_sections_locally (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (U : X.Opens)
    (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens), ∃ _hVU : V ≤ U, x ∈ V ∧
      ∃ (a : Γ((LineBundleDual.Construction.lineBundleDual L).sheaf, V)) (s : Γ(L.sheaf, V)),
        TensorHom.Construction.internalHomEval L.sheaf (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) V a s = (1 : Γ(X, V)) := by
  obtain ⟨W, hxW, ⟨e⟩⟩ := L.locallyTrivial x
  let V := U ⊓ W
  let eV := LineBundleEpi.Construction.moduleFrameRestrict L.sheaf (show V ≤ W from inf_le_right) e
  let e' := (Scheme.Modules.restrictFunctorIsoPullback V.ι).app L.sheaf ≪≫ eV
  have he := dual_sections_of_frame V.ι L.sheaf e' ⊤
  erw [Scheme.Opens.ι_image_top] at he
  exact ⟨V, inf_le_left, ⟨hx, hxW⟩, he⟩

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundlePairing
