import OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.GlobalFunctions
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Affine Base Change -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.AffineBaseChange.Construction

noncomputable section

/-!
# Completion: global functions after affine base change of a proper geometric scheme

Flat base change identifies the global functions on X × Y with those on Y
when X is proper integral over an algebraically closed field and Y is affine.
This is the function-theoretic input for the product rigidity argument.
-/

open _root_.CategoryTheory Limits _root_.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {X Y : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of K)) [IsIntegral X] [IsProper p]
  (q : Y ⟶ Spec (CommRingCat.of K)) [IsAffine Y]

/-- The structure projection induces an isomorphism of global section rings. -/
theorem properIntegral_affineBaseChange_appTop_isIso :
    IsIso (pullback.snd p q).appTop := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated p
  have hp : IsIso p.appTop := GlobalFunctions.Construction.properIntegral_appTop_isIso p
  have h := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback p q) (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
    (by simp) (by simp) (by simp) (isAffineOpen_top _) (isAffineOpen_top _)
    isCompact_univ isQuasiSeparated_univ
  have hs := (isIso_pushoutSection_iff
    (IsPullback.of_hasPullback p q) (US := ⊤) (UT := ⊤) (UX := ⊤) (UY := ⊤)
    (by simp) (by simp) (by simp)).mp h
  have hs' : IsPushout p.appTop q.appTop (pullback.fst p q).appTop (pullback.snd p q).appTop := by
    simpa only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, TopologicalSpace.Opens.map_top] using hs
  exact hs'.isIso_inr_of_isIso

/-- The axis supplied by a section of the proper factor. -/
def properProductSection (e : Spec (CommRingCat.of K) ⟶ X) (he : e ≫ p = 𝟙 _) :
    Y ⟶ pullback p q :=
  pullback.lift (q ≫ e) (𝟙 Y) (by simp [Category.assoc, he])

/-- Every map from the product to an affine scheme factors through the affine base. -/
theorem properIntegral_product_to_affine {Z : Scheme.{u}} [IsAffine Z]
    (e : Spec (CommRingCat.of K) ⟶ X) (he : e ≫ p = 𝟙 _)
    (f : pullback p q ⟶ Z) :
    f = pullback.snd p q ≫ properProductSection p q e he ≫ f := by
  have : IsIso (pullback.snd p q).appTop := properIntegral_affineBaseChange_appTop_isIso p q
  have h : (pullback.snd p q).appTop ≫ (properProductSection p q e he).appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop]
    change (pullback.lift (q ≫ e) (𝟙 Y) _ ≫ pullback.snd p q).appTop = _
    rw [pullback.lift_snd, Scheme.Hom.id_appTop]
  have h' : (properProductSection p q e he).appTop ≫ (pullback.snd p q).appTop = 𝟙 _ := by
    rw [← cancel_epi (pullback.snd p q).appTop, ← Category.assoc, h]
    simp
  apply ext_of_isAffine
  simp only [Scheme.Hom.comp_appTop, ← Category.assoc, h', Category.comp_id]

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Proper.AffineBaseChange.Construction
