import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Gluing

/-! # Gluing Comparison -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.GluingComparison

noncomputable section

/-!
# Pullback compatibility of the affine presentation of gluing
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- Rearrange two commuting squares of isomorphisms while retaining their prescribed maps. -/
theorem rearrange {C : Type*} [Category C] {X Y Z W P Q U : C}
    (a : X ≅ Y) (b : Y ≅ Z) (c : Z ≅ W) (d : X ≅ P) (v : P ≅ W)
    (r : P ≅ Q) (s : X ≅ U) (t : U ≅ Q)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ v.hom)
    (hn : s.hom ≫ t.hom = d.hom ≫ r.hom) :
    c.hom ≫ v.inv ≫ r.hom = b.inv ≫ a.inv ≫ s.hom ≫ t.hom := by
  calc
    _ = b.inv ≫ a.inv ≫ (a.hom ≫ b.hom ≫ c.hom) ≫ v.inv ≫ r.hom := by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    _ = b.inv ≫ a.inv ≫ (d.hom ≫ v.hom) ≫ v.inv ≫ r.hom := by rw [h]
    _ = _ := by rw [hn]; simp only [Category.assoc, Iso.hom_inv_id_assoc]

open OAI.AlgebraicGeometry.Picard.PoincareBundle.TildePullback OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Composition OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Gluing

variable {R S T : CommRingCat.{u}} (M : ModuleCat.{u} R)
  {L : (Spec R).Modules} (e : (tilde.functor R).obj M ≅ L)

/-- The affine presentation comparison respects an additional geometric pullback. -/
theorem comparison_composition (f : R ⟶ S) (g : S ⟶ T) :
    (tilde.functor T).map ((ModuleCat.extendScalarsComp f.hom g.hom).inv.app M) ≫
        (Affine.Gluing.comparison M e (f ≫ g)).hom =
      (TildePullback.tildePullbackIso g).inv.app ((ModuleCat.extendScalars f.hom).obj M) ≫
        (Scheme.Modules.pullback (Spec.map g)).map ((Affine.Gluing.comparison M e f).hom) ≫
          (Affine.Composition.geometricCompositionIso f g).hom.app L := by
  have h := rearrange
    ((Scheme.Modules.pullback (Spec.map g)).mapIso ((TildePullback.tildePullbackIso f).app M))
    ((TildePullback.tildePullbackIso g).app ((ModuleCat.extendScalars f.hom).obj M))
    ((tilde.functor T).mapIso ((ModuleCat.extendScalarsComp f.hom g.hom).app M).symm)
    ((Affine.Composition.geometricCompositionIso f g).app ((tilde.functor R).obj M))
    ((TildePullback.tildePullbackIso (f ≫ g)).app M)
    ((Scheme.Modules.pullback (Spec.map (f ≫ g))).mapIso e)
    ((Scheme.Modules.pullback (Spec.map f) ⋙ Scheme.Modules.pullback (Spec.map g)).mapIso e)
    ((Affine.Composition.geometricCompositionIso f g).app L)
    (Affine.Composition.tilde_composition_app f g M) ((Affine.Composition.geometricCompositionIso f g).hom.naturality e.hom)
  simpa only [Affine.Gluing.comparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Functor.comp_map,
    CategoryTheory.Functor.map_comp, Category.assoc] using h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.GluingComparison
