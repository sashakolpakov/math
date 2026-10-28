import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PullbackCoherence
import OAI.RepresentationTheory.Theta.Geometric.TranslatedLineIsoPullback

/-! # Translated Restrictions -/

namespace OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TranslatedRestrictions

noncomputable section

/-! Exact restrictions of glued translation comparisons persist on
any test scheme mapping into a label fiber. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations
universe u

theorem nativePullback_translatedMapLineIso {X T U : Scheme.{u}} (M : X.Modules) (t : X ⟶ X)
    (e : (Scheme.Modules.pullback t).obj M ≅ M) (x y : T ⟶ X) (h : y = x ≫ t)
    (r : U ⟶ T) (x' y' : U ⟶ X) (hx : r ≫ x = x') (hy : r ≫ y = y') (h' : y' = x' ≫ t) :
    AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback (LocallyTranslatedLineIso.translatedMapLineIso M t e x y h).hom r y' x' hy hx =
      (LocallyTranslatedLineIso.translatedMapLineIso M t e x' y' h').hom := by
  subst x'
  subst y'
  exact TranslatedLineIsoPullback.translatedMapLineIso_pullback M t e x y h r h'

theorem nativePullback_restrictedTranslatedMapLineIso {X T : Scheme.{u}} (M : X.Modules) (t : X ⟶ X)
    (e : (Scheme.Modules.pullback t).obj M ≅ M) (x y : T ⟶ X) (U : T.Opens)
    (h : U.ι ≫ y = (U.ι ≫ x) ≫ t)
    (φ : (Scheme.Modules.pullback y).obj M ⟶ (Scheme.Modules.pullback x).obj M)
    (hφ : (Scheme.Modules.pullback U.ι).map φ = (LocallyTranslatedLineIso.restrictedTranslatedMapLineIso M t e x y U h).hom) :
    AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback φ U.ι (U.ι ≫ y) (U.ι ≫ x) rfl rfl =
      (LocallyTranslatedLineIso.translatedMapLineIso M t e (U.ι ≫ x) (U.ι ≫ y) h).hom := by
  change ((Scheme.Modules.pullbackComp U.ι y).app M).inv ≫
    (Scheme.Modules.pullback U.ι).map φ ≫ ((Scheme.Modules.pullbackComp U.ι x).app M).hom = _
  rw [hφ]
  simp only [LocallyTranslatedLineIso.restrictedTranslatedMapLineIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

theorem nativePullback_glued_translation_on_fiber {X T V : Scheme.{u}} (M : X.Modules) (t : X ⟶ X)
    (e : (Scheme.Modules.pullback t).obj M ≅ M) (x y : T ⟶ X) (U : T.Opens)
    (h : U.ι ≫ y = (U.ι ≫ x) ≫ t)
    (φ : (Scheme.Modules.pullback y).obj M ⟶ (Scheme.Modules.pullback x).obj M)
    (hφ : (Scheme.Modules.pullback U.ι).map φ = (LocallyTranslatedLineIso.restrictedTranslatedMapLineIso M t e x y U h).hom)
    (r : V ⟶ U.toScheme) (hx : (r ≫ U.ι) ≫ y = ((r ≫ U.ι) ≫ x) ≫ t) :
    AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback φ (r ≫ U.ι) ((r ≫ U.ι) ≫ y) ((r ≫ U.ι) ≫ x) rfl rfl =
      (LocallyTranslatedLineIso.translatedMapLineIso M t e ((r ≫ U.ι) ≫ x) ((r ≫ U.ι) ≫ y) hx).hom := by
  have hnest := PullbackCoherence.nativePullback_nested φ U.ι (U.ι ≫ y) (U.ι ≫ x) rfl rfl r
    ((r ≫ U.ι) ≫ y) ((r ≫ U.ι) ≫ x) (Category.assoc r U.ι y).symm (Category.assoc r U.ι x).symm
  rw [nativePullback_restrictedTranslatedMapLineIso M t e x y U h φ hφ] at hnest
  exact hnest.symm.trans (nativePullback_translatedMapLineIso M t e _ _ h r _ _ _ _ hx)

theorem nativePullback_glued_translation_of_factor {X T V : Scheme.{u}} (M : X.Modules) (t : X ⟶ X)
    (e : (Scheme.Modules.pullback t).obj M ≅ M) (x y : T ⟶ X) (U : T.Opens)
    (h : U.ι ≫ y = (U.ι ≫ x) ≫ t)
    (φ : (Scheme.Modules.pullback y).obj M ⟶ (Scheme.Modules.pullback x).obj M)
    (hφ : (Scheme.Modules.pullback U.ι).map φ = (LocallyTranslatedLineIso.restrictedTranslatedMapLineIso M t e x y U h).hom)
    (r : V ⟶ T) (s : V ⟶ U.toScheme) (hs : s ≫ U.ι = r)
    (x' y' : V ⟶ X) (hx : r ≫ x = x') (hy : r ≫ y = y') (h' : y' = x' ≫ t) :
    AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback φ r y' x' hy hx = (LocallyTranslatedLineIso.translatedMapLineIso M t e x' y' h').hom := by
  subst r
  have hnest := PullbackCoherence.nativePullback_nested φ U.ι (U.ι ≫ y) (U.ι ≫ x) rfl rfl s y' x'
    ((Category.assoc s U.ι y).symm.trans hy) ((Category.assoc s U.ι x).symm.trans hx)
  rw [nativePullback_restrictedTranslatedMapLineIso M t e x y U h φ hφ] at hnest
  exact hnest.symm.trans (nativePullback_translatedMapLineIso M t e _ _ h s x' y' _ _ h')

end

end OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TranslatedRestrictions
