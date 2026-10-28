import OAI.RepresentationTheory.Theta.Geometric.Normalized.TranslationFrames
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.PullbackCoherence
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TranslatedRestrictions

/-! # Normalized Frames -/

namespace OAI.RepresentationTheory.Theta.Geometric.Local.NormalizedFrames

noncomputable section

/-! Normalization of a comparison is detected on an open cover,
using the native frames induced from a fixed axis. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations
universe u

theorem normalizedTranslation_fiber_frame_eq {X Y T : Scheme.{u}} (M : X.Modules)
    (t : X ⟶ X) (i : Y ⟶ X) (a : Y ⟶ Y) (hi : a ≫ i = i ≫ t)
    (e : (Scheme.Modules.pullback i).obj M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y)
    (θ : (Scheme.Modules.pullback t).obj M ≅ M)
    (hθ : (Scheme.Modules.pullback i).mapIso θ ≪≫ e = Pullback.SquareFrames.pullbackSquareFrame t i i a hi M e)
    (v w : T ⟶ Y) (hw : w = v ≫ a) (hv : w ≫ i = (v ≫ i) ≫ t) :
    LocallyTranslatedLineIso.translatedMapLineIso M t θ (v ≫ i) (w ≫ i) hv ≪≫ FactoredPullbackFrames.factoredPullbackFrame v i e =
      FactoredPullbackFrames.factoredPullbackFrame w i e := by
  subst w
  exact Normalized.TranslationFrames.normalizedTranslation_fiber_frame M t i a hi e θ hθ v hv

theorem factoredFrames_normalization_of_open_cover {X Y T : Scheme.{u}} (M : X.Modules)
    (i : Y ⟶ X) (e : (Scheme.Modules.pullback i).obj M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y)
    (v w : T ⟶ Y)
    (φ : (Scheme.Modules.pullback (w ≫ i)).obj M ⟶ (Scheme.Modules.pullback (v ≫ i)).obj M)
    {I : Type u} (U : I → T.Opens) (hU : iSup U = ⊤)
    (h : ∀ a, AlgebraicGeometry.Picard.PoincareBundle.Geometric.DescentEquations.nativePullback φ (U a).ι ((U a).ι ≫ w ≫ i) ((U a).ι ≫ v ≫ i) rfl rfl ≫
      (FactoredPullbackFrames.factoredPullbackFrame ((U a).ι ≫ v) i e).hom =
        (FactoredPullbackFrames.factoredPullbackFrame ((U a).ι ≫ w) i e).hom) :
    φ ≫ (FactoredPullbackFrames.factoredPullbackFrame v i e).hom = (FactoredPullbackFrames.factoredPullbackFrame w i e).hom := by
  apply AlgebraicGeometry.Quotients.FiniteDescent.ReducedSectionsEq.Construction.ReducedSections.moduleMap_eq_of_locally
  intro t
  have ht : t ∈ iSup U := hU.symm ▸ (show t ∈ (⊤ : T.Opens) from trivial)
  obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp ht
  refine ⟨U a, ha, ?_⟩
  apply (cancel_epi ((Scheme.Modules.pullbackComp (U a).ι (w ≫ i)).app M).inv).mp
  apply (cancel_mono (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso (U a).ι).hom).mp
  have hv := congrArg Iso.hom (FactoredPullbackFrames.factoredPullbackFrame_comp (U a).ι v i e)
  have hw := congrArg Iso.hom (FactoredPullbackFrames.factoredPullbackFrame_comp (U a).ι w i e)
  have H := h a
  rw [← hv, ← hw] at H
  change ((Scheme.Modules.pullbackComp (U a).ι (w ≫ i)).app M).inv ≫
      (Scheme.Modules.pullback (U a).ι).map φ ≫
      ((Scheme.Modules.pullbackComp (U a).ι (v ≫ i)).app M).hom ≫
      (((Scheme.Modules.pullbackComp (U a).ι (v ≫ i)).app M).inv ≫
        (Scheme.Modules.pullback (U a).ι).map (FactoredPullbackFrames.factoredPullbackFrame v i e).hom ≫
        (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso (U a).ι).hom) =
    ((Scheme.Modules.pullbackComp (U a).ι (w ≫ i)).app M).inv ≫
      (Scheme.Modules.pullback (U a).ι).map (FactoredPullbackFrames.factoredPullbackFrame w i e).hom ≫
      (AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.pullbackUnitIso (U a).ι).hom at H
  simpa only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc] using H

theorem locallyTranslatedIso_axis_frame {X Y T : Scheme.{u}} (M : X.Modules)
    (i : Y ⟶ X) (e : (Scheme.Modules.pullback i).obj M ≅ AlgebraicGeometry.SheafCohomology.Projective.Invertible.Scheme.Modules.unitObj Y)
    {I : Type u} (t : I → (X ⟶ X)) (a : I → (Y ⟶ Y))
    (hi : ∀ b, a b ≫ i = i ≫ t b)
    (θ : ∀ b, (Scheme.Modules.pullback (t b)).obj M ≅ M)
    (hθ : ∀ b, (Scheme.Modules.pullback i).mapIso (θ b) ≪≫ e =
      Pullback.SquareFrames.pullbackSquareFrame (t b) i i (a b) (hi b) M e)
    (U : I → T.Opens) (hU : iSup U = ⊤) (v w : T ⟶ Y)
    (hw : ∀ b, (U b).ι ≫ w = ((U b).ι ≫ v) ≫ a b)
    (hv : ∀ b, (U b).ι ≫ w ≫ i = ((U b).ι ≫ v ≫ i) ≫ t b)
    (φ : (Scheme.Modules.pullback (w ≫ i)).obj M ⟶ (Scheme.Modules.pullback (v ≫ i)).obj M)
    (hφ : ∀ b, (Scheme.Modules.pullback (U b).ι).map φ =
      (LocallyTranslatedLineIso.restrictedTranslatedMapLineIso M (t b) (θ b) (v ≫ i) (w ≫ i) (U b) (hv b)).hom) :
    φ ≫ (FactoredPullbackFrames.factoredPullbackFrame v i e).hom = (FactoredPullbackFrames.factoredPullbackFrame w i e).hom := by
  apply factoredFrames_normalization_of_open_cover M i e v w φ U hU
  intro b
  have hd := Intrinsic.TranslatedRestrictions.nativePullback_restrictedTranslatedMapLineIso M (t b) (θ b)
    (v ≫ i) (w ≫ i) (U b) (hv b) φ (hφ b)
  have hn := normalizedTranslation_fiber_frame_eq M (t b) i (a b) (hi b) e
    (θ b) (hθ b) ((U b).ι ≫ v) ((U b).ι ≫ w) (hw b) (hv b)
  exact (congrArg (fun f => f ≫ (FactoredPullbackFrames.factoredPullbackFrame ((U b).ι ≫ v) i e).hom) hd).trans
    (congrArg Iso.hom hn)

end

end OAI.RepresentationTheory.Theta.Geometric.Local.NormalizedFrames
