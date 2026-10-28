import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Composition
import OAI.AlgebraicGeometry.Picard.PoincareBundle.QuasiCoherent

/-! # Gluing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Gluing

noncomputable section

/-!
# Transporting actual geometric affine gluing to modules
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.TildePullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Composition

variable {R S T : CommRingCat.{u}} (M : ModuleCat.{u} R)
  {L : (Spec R).Modules} (e : (tilde.functor R).obj M ≅ L)

/-- The geometric pullback of a chosen affine module presentation. -/
def comparison (f : R ⟶ S) :
    (tilde.functor S).obj ((ModuleCat.extendScalars f.hom).obj M) ≅
      (Scheme.Modules.pullback (Spec.map f)).obj L :=
  ((TildePullback.tildePullbackIso f).app M).symm ≪≫ (Scheme.Modules.pullback (Spec.map f)).mapIso e

/-- A geometric gluing morphism determines a unique map of the actual scalar extensions. -/
def moduleHom (f g : R ⟶ S)
    (a : (Scheme.Modules.pullback (Spec.map f)).obj L ⟶
      (Scheme.Modules.pullback (Spec.map g)).obj L) :
    (ModuleCat.extendScalars f.hom).obj M ⟶ (ModuleCat.extendScalars g.hom).obj M :=
  (tilde.fullyFaithfulFunctor (R := S)).preimage
    ((comparison M e f).hom ≫ a ≫ (comparison M e g).inv)

/-- Sheafification recovers the original geometric gluing map with its specified comparisons. -/
theorem map_moduleHom (f g : R ⟶ S)
    (a : (Scheme.Modules.pullback (Spec.map f)).obj L ⟶
      (Scheme.Modules.pullback (Spec.map g)).obj L) :
    (tilde.functor S).map (moduleHom M e f g a) =
      (comparison M e f).hom ≫ a ≫ (comparison M e g).inv :=
  (tilde.fullyFaithfulFunctor (R := S)).map_preimage _

/-- A geometric affine gluing isomorphism gives an actual module gluing isomorphism. -/
def moduleIso (f g : R ⟶ S)
    (a : (Scheme.Modules.pullback (Spec.map f)).obj L ≅
      (Scheme.Modules.pullback (Spec.map g)).obj L) :
    (ModuleCat.extendScalars f.hom).obj M ≅ (ModuleCat.extendScalars g.hom).obj M :=
  (tilde.fullyFaithfulFunctor (R := S)).preimageIso
    (comparison M e f ≪≫ a ≪≫ (comparison M e g).symm)

/-- Gluing and its module transport have the same underlying homomorphism. -/
theorem moduleIso_hom (f g : R ⟶ S)
    (a : (Scheme.Modules.pullback (Spec.map f)).obj L ≅
      (Scheme.Modules.pullback (Spec.map g)).obj L) :
    (moduleIso M e f g a).hom = moduleHom M e f g a.hom := rfl

/-- Transfer of gluing preserves composition. -/
theorem moduleHom_comp (f g h : R ⟶ S)
    (a : (Scheme.Modules.pullback (Spec.map f)).obj L ⟶
      (Scheme.Modules.pullback (Spec.map g)).obj L)
    (b : (Scheme.Modules.pullback (Spec.map g)).obj L ⟶
      (Scheme.Modules.pullback (Spec.map h)).obj L) :
    moduleHom M e f g a ≫ moduleHom M e g h b = moduleHom M e f h (a ≫ b) := by
  apply (tilde.functor S).map_injective
  rw [(tilde.functor S).map_comp, map_moduleHom, map_moduleHom, map_moduleHom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- Transfer of gluing preserves the identity map. -/
theorem moduleHom_id (f : R ⟶ S) : moduleHom M e f f (𝟙 _) = 𝟙 _ := by
  apply (tilde.functor S).map_injective
  rw [map_moduleHom, (tilde.functor S).map_id, Category.id_comp, Iso.hom_inv_id]

/-- Equal coordinate maps induce the same transport on geometric and module gluing. -/
theorem moduleHom_congr {f f' g g' : R ⟶ S} (hf : f = f') (hg : g = g')
    (a : (Scheme.Modules.pullback (Spec.map f)).obj L ⟶
      (Scheme.Modules.pullback (Spec.map g)).obj L) :
    moduleHom M e f' g'
        (eqToHom (congrArg (fun r => (Scheme.Modules.pullback (Spec.map r)).obj L) hf.symm) ≫
          a ≫ eqToHom (congrArg (fun r => (Scheme.Modules.pullback (Spec.map r)).obj L) hg)) =
      eqToHom (congrArg (fun r : R ⟶ S => (ModuleCat.extendScalars r.hom).obj M) hf.symm) ≫
        moduleHom M e f g a ≫
          eqToHom (congrArg (fun r : R ⟶ S => (ModuleCat.extendScalars r.hom).obj M) hg) := by
  subst f'
  subst g'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Gluing
