import OAI.AlgebraicGeometry.Picard.PoincareBundle.GluingComparison
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GluingTransport

/-! # Gluing Pullback -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.GluingPullback

noncomputable section

/-!
# Scalar extension of geometric affine gluing
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.TildePullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Composition OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Gluing OAI.AlgebraicGeometry.Picard.PoincareBundle.GluingComparison

variable {R S T : CommRingCat.{u}} (M : ModuleCat.{u} R)
  {L : (Spec R).Modules} (e : (tilde.functor R).obj M ≅ L)

/-- Geometric pullback of a gluing map, expressed on the two composite base maps. -/
def geometricHom (f g : R ⟶ S) (k : S ⟶ T)
    (a : (Scheme.Modules.pullback (Spec.map f)).obj L ⟶
      (Scheme.Modules.pullback (Spec.map g)).obj L) :
    (Scheme.Modules.pullback (Spec.map (f ≫ k))).obj L ⟶
      (Scheme.Modules.pullback (Spec.map (g ≫ k))).obj L :=
  (Composition.geometricCompositionIso f k).inv.app L ≫ (Scheme.Modules.pullback (Spec.map k)).map a ≫
    (Composition.geometricCompositionIso g k).hom.app L

/-- Extending the transferred module gluing equals transferring the geometric pullback of gluing. -/
theorem moduleHom_baseChange (f g : R ⟶ S) (k : S ⟶ T)
    (a : (Scheme.Modules.pullback (Spec.map f)).obj L ⟶
      (Scheme.Modules.pullback (Spec.map g)).obj L) :
    (ModuleCat.extendScalarsComp f.hom k.hom).hom.app M ≫
        (ModuleCat.extendScalars k.hom).map (Gluing.moduleHom M e f g a) ≫
          (ModuleCat.extendScalarsComp g.hom k.hom).inv.app M =
      Gluing.moduleHom M e (f ≫ k) (g ≫ k) (geometricHom f g k a) := by
  have ht := GluingTransport.transfer (tilde.functor S) (ModuleCat.extendScalars k.hom)
    (Scheme.Modules.pullback (Spec.map k)) (tilde.functor T) (TildePullback.tildePullbackIso k)
    ((ModuleCat.extendScalarsComp f.hom k.hom).app M)
    ((ModuleCat.extendScalarsComp g.hom k.hom).app M)
    (Gluing.comparison M e f) (Gluing.comparison M e g) (Gluing.moduleHom M e f g a) a (Gluing.map_moduleHom M e f g a)
  have hf := GluingTransport.comparison (tilde.functor T)
    (Scheme.Modules.pullback (Spec.map k))
    ((ModuleCat.extendScalarsComp f.hom k.hom).app M)
    ((TildePullback.tildePullbackIso k).app ((ModuleCat.extendScalars f.hom).obj M))
    (Gluing.comparison M e f) (Gluing.comparison M e (f ≫ k)) ((Composition.geometricCompositionIso f k).app L)
    (GluingComparison.comparison_composition M e f k)
  have hg := GluingTransport.comparison (tilde.functor T)
    (Scheme.Modules.pullback (Spec.map k))
    ((ModuleCat.extendScalarsComp g.hom k.hom).app M)
    ((TildePullback.tildePullbackIso k).app ((ModuleCat.extendScalars g.hom).obj M))
    (Gluing.comparison M e g) (Gluing.comparison M e (g ≫ k)) ((Composition.geometricCompositionIso g k).app L)
    (GluingComparison.comparison_composition M e g k)
  rw [hf, hg] at ht
  apply (tilde.functor T).map_injective
  rw [Gluing.map_moduleHom]
  simpa only [geometricHom, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Iso.app_hom, Iso.app_inv, Category.assoc] using ht

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.GluingPullback
