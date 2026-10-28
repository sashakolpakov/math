import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.OpenRestriction
import OAI.AlgebraicGeometry.DivisorClass.Chern.FramesFrame

/-! # Frame Transport -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.FrameTransport

noncomputable section

/-!
# ChernClass: actual section frames under open immersion

The genuine section and scalar isomorphisms transport a frame of the
original sheaf to its restriction. Both restriction maps and transition
units commute with this construction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Construction

variable {X Y : Scheme} (f : Y ⟶ X) [IsOpenImmersion f] (M : X.Modules)

/-- Transport a section frame through the actual open-immersion section isomorphisms. -/
def openImmersionSectionFrame (W : Y.Opens)
    (e : Γ(M, f ''ᵁ W) ≃ₗ[Γ(X, f ''ᵁ W)] Γ(X, f ''ᵁ W)) :
    Γ(M.restrict f, W) ≃ₗ[Γ(Y, W)] Γ(Y, W) where
  toFun m := (f.appIso W).hom (e ((M.restrictAppIso f W).hom m))
  invFun r := (M.restrictAppIso f W).inv (e.symm ((f.appIso W).inv r))
  left_inv m := by
    dsimp only
    rw [Iso.hom_inv_id_apply, e.symm_apply_apply, Iso.hom_inv_id_apply]
  right_inv r := by
    dsimp only
    rw [Iso.inv_hom_id_apply, e.apply_symm_apply, Iso.inv_hom_id_apply]
  map_add' m n := by simp only [map_add]
  map_smul' r m := by
    have h := ConcreteCategory.congr_hom (Scheme.Modules.smul_restrictAppIso_hom f M W r) m
    change (M.restrictAppIso f W).hom (r • m) =
      ((f.appIso W).inv r) • (M.restrictAppIso f W).hom m at h
    rw [h, e.map_smul]
    change (f.appIso W).hom ((f.appIso W).inv r * e ((M.restrictAppIso f W).hom m)) = _
    rw [map_mul, Iso.inv_hom_id_apply]
    rfl

/-- The transported frames preserve compatibility with genuine module restrictions. -/
theorem openImmersionSectionFrame_naturality {V W : Y.Opens} (h : V ≤ W)
    (eW : Γ(M, f ''ᵁ W) ≃ₗ[Γ(X, f ''ᵁ W)] Γ(X, f ''ᵁ W))
    (eV : Γ(M, f ''ᵁ V) ≃ₗ[Γ(X, f ''ᵁ V)] Γ(X, f ''ᵁ V))
    (he : ∀ m, eV (M.presheaf.map (homOfLE (f.image_mono h)).op m) =
      X.presheaf.map (homOfLE (f.image_mono h)).op (eW m))
    (m : Γ(M.restrict f, W)) :
    openImmersionSectionFrame f M V eV ((M.restrict f).presheaf.map (homOfLE h).op m) =
      Y.presheaf.map (homOfLE h).op (openImmersionSectionFrame f M W eW m) := by
  change (f.appIso V).hom (eV ((M.restrictAppIso f V).hom _)) = _
  rw [Scheme.Modules.map_restrictAppIso_hom_apply, he]
  exact ConcreteCategory.congr_hom (f.appIso_hom_naturality (homOfLE h).op) _

/-- Actual transition units pull back by the scalar isomorphism. -/
theorem openImmersionSectionFrame_transition (W : Y.Opens)
    (e e' : Γ(M, f ''ᵁ W) ≃ₗ[Γ(X, f ''ᵁ W)] Γ(X, f ''ᵁ W)) :
    FramesFrame.Construction.frameTransitionUnit (openImmersionSectionFrame f M W e)
      (openImmersionSectionFrame f M W e') =
      Units.map (f.appIso W).hom.hom.toMonoidHom (FramesFrame.Construction.frameTransitionUnit e e') := by
  apply Units.ext
  change (f.appIso W).hom
      (e ((M.restrictAppIso f W).hom ((M.restrictAppIso f W).inv
        (e'.symm ((f.appIso W).inv 1))))) =
    (f.appIso W).hom (e (e'.symm 1))
  rw [Iso.inv_hom_id_apply, map_one]

end Construction

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.FrameTransport
