import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.FrameComparison

/-! # Open Frames -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenFrames.Cycles.LineBundleConstruction

/-!
# LineBundleCycles: actual section frames under open immersion

The genuine section and scalar isomorphisms transport a frame of the
original sheaf to its restriction. Both restriction maps and transition
units commute with this construction.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

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
    FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit (openImmersionSectionFrame f M W e)
      (openImmersionSectionFrame f M W e') =
      Units.map (f.appIso W).hom.hom.toMonoidHom (FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit e e') := by
  apply Units.ext
  change (f.appIso W).hom
      (e ((M.restrictAppIso f W).hom ((M.restrictAppIso f W).inv
        (e'.symm ((f.appIso W).inv 1))))) =
    (f.appIso W).hom (e (e'.symm 1))
  rw [Iso.inv_hom_id_apply, map_one]

end AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenFrames.Cycles.LineBundleConstruction

namespace AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenFrames.Cycles.SchemeLineBundle

/-!
# LineBundleCycles: compare original frames with frames of the restricted line bundle

The actual section identifications compare the original algebraic atlas
with the restricted sheaf's independently chosen atlas. Their mixed units
satisfy restriction and change-of-frame identities in the actual section rings.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X)
  (f : Y ⟶ X) [IsOpenImmersion f]

local notation "M" => L.restrictToOpen f

/-- The original frame, transported to sections of the actual restricted sheaf. -/
def _root_.OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openSectionFrame (i : X) (W : Y.Opens)
    (hi : f ''ᵁ W ≤ L.trivializingOpen i) :
    Γ((M).sheaf, W) ≃ₗ[Γ(Y, W)] Γ(Y, W) :=
  LineBundleConstruction.openImmersionSectionFrame f L.sheaf W (L.sectionFrame i (f ''ᵁ W) hi)

theorem _root_.OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openSectionFrame_naturality (i : X) {V W : Y.Opens}
    (hVW : V ≤ W) (hi : f ''ᵁ W ≤ L.trivializingOpen i) (m : Γ((M).sheaf, W)) :
    L.openSectionFrame f i V ((f.image_mono hVW).trans hi)
        ((M).sheaf.presheaf.map (homOfLE hVW).op m) =
      Y.presheaf.map (homOfLE hVW).op (L.openSectionFrame f i W hi m) :=
  LineBundleConstruction.openImmersionSectionFrame_naturality f L.sheaf hVW _ _
    (L.sectionFrame_naturality i (f.image_mono hVW) hi) m

/-- The transported transition is the actual scalar pullback of the original unit. -/
theorem _root_.OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openSectionFrame_transition (i j : X) (W : Y.Opens)
    (hi : f ''ᵁ W ≤ L.trivializingOpen i) (hj : f ''ᵁ W ≤ L.trivializingOpen j) :
    FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit (L.openSectionFrame f i W hi) (L.openSectionFrame f j W hj) =
      Units.map (f.appIso W).hom.hom.toMonoidHom
        (L.ambientTransitionOn i j (f ''ᵁ W) hi hj) :=
  LineBundleConstruction.openImmersionSectionFrame_transition f L.sheaf W _ _

/-- A regular unit comparing an original frame with a native restricted-sheaf frame. -/
def _root_.OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openMixedTransitionOn (i : X) (j : Y) (W : Y.Opens)
    (hi : f ''ᵁ W ≤ L.trivializingOpen i) (hj : W ≤ (M).trivializingOpen j) :
    Γ(Y, W)ˣ :=
  FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit (L.openSectionFrame f i W hi) ((M).sectionFrame j W hj)

theorem _root_.OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openMixedTransitionOn_restrict (i : X) (j : Y)
    {V W : Y.Opens} (hVW : V ≤ W)
    (hi : f ''ᵁ W ≤ L.trivializingOpen i) (hj : W ≤ (M).trivializingOpen j) :
    Units.map (Y.presheaf.map (homOfLE hVW).op).hom.toMonoidHom
      (L.openMixedTransitionOn f i j W hi hj) =
      L.openMixedTransitionOn f i j V ((f.image_mono hVW).trans hi) (hVW.trans hj) :=
  FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit_map (Y.presheaf.map (homOfLE hVW).op).hom
    ((M).sheaf.presheaf.map (homOfLE hVW).op) _ _ _ _
    (L.openSectionFrame_naturality f i hVW hi) ((M).sectionFrame_naturality j hVW hj)

/-- Actual original, restricted, and mixed transitions form a commuting square. -/
theorem _root_.OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle.openMixedTransitionOn_square (i j : X) (k l : Y)
    (W : Y.Opens)
    (hi : f ''ᵁ W ≤ L.trivializingOpen i) (hj : f ''ᵁ W ≤ L.trivializingOpen j)
    (hk : W ≤ (M).trivializingOpen k) (hl : W ≤ (M).trivializingOpen l) :
    L.openMixedTransitionOn f i k W hi hk * (M).ambientTransitionOn k l W hk hl =
      Units.map (f.appIso W).hom.hom.toMonoidHom
        (L.ambientTransitionOn i j (f ''ᵁ W) hi hj) *
      L.openMixedTransitionOn f j l W hj hl := by
  rw [← L.openSectionFrame_transition f i j W hi hj]
  exact (FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit_cocycle _ _ _).trans (FrameComparison.Cycles.LineBundleConstruction.frameTransitionUnit_cocycle _ _ _).symm

end AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenFrames.Cycles.SchemeLineBundle

end

end OAI
