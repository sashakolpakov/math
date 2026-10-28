import OAI.AlgebraicGeometry.Picard.PoincareBundle.GluingComparison

/-! # Comparison Congr -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.ComparisonCongr

noncomputable section

/-!
# Affine presentations respect equal coordinate maps and iterated pullbacks
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Gluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Composition

variable {R S T : CommRingCat.{u}} (M : ModuleCat.{u} R)
  {L : (Spec R).Modules} (e : (tilde.functor R).obj M ≅ L)

/-- The presentation comparison uses the inverse tilde map followed by the pulled-back presentation. -/
theorem comparison_hom (f : R ⟶ S) :
    (Gluing.comparison M e f).hom =
      (TildePullback.tildePullbackIso f).inv.app M ≫
        (Scheme.Modules.pullback (Spec.map f)).map e.hom := rfl

/-- Equal affine coordinate maps give the same presentation, with the standard transport. -/
theorem comparison_congr {f g : R ⟶ S} (h : f = g) :
    (tilde.functor S).map
        (eqToHom (congrArg (fun r : R ⟶ S => (ModuleCat.extendScalars r.hom).obj M) h)) ≫
      (Gluing.comparison M e g).hom =
    (Gluing.comparison M e f).hom ≫
      (Scheme.Modules.pullbackCongr (congrArg Spec.map h)).hom.app L := by
  subst g
  change (tilde.functor S).map (𝟙 _) ≫ (Gluing.comparison M e f).hom =
    (Gluing.comparison M e f).hom ≫ 𝟙 _
  rw [(tilde.functor S).map_id, Category.id_comp, Category.comp_id]

/-- The composition theorem expressed directly with the two chosen affine presentations. -/
theorem comparison_composition (f : R ⟶ S) (g : S ⟶ T) :
    (tilde.functor T).map ((ModuleCat.extendScalarsComp f.hom g.hom).inv.app M) ≫
      (Gluing.comparison M e (f ≫ g)).hom =
    (Gluing.comparison ((ModuleCat.extendScalars f.hom).obj M) (Gluing.comparison M e f) g).hom ≫
      (Composition.geometricCompositionIso f g).hom.app L := by
  have hc := comparison_hom ((ModuleCat.extendScalars f.hom).obj M) (Gluing.comparison M e f) g
  have ht := GluingComparison.comparison_composition M e f g
  exact ht.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (fun z => z ≫ (Composition.geometricCompositionIso f g).hom.app L) hc.symm))

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.ComparisonCongr
