import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.ComparisonCongr

/-! # Comparison Isos -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.ComparisonIsos

noncomputable section

/-!
# Affine composition and equality comparisons as equations of whole isomorphisms
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Gluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Composition

variable {R S T : CommRingCat.{u}} (M : ModuleCat.{u} R)
  {L : (Spec R).Modules} (e : (tilde.functor R).obj M ≅ L)

/-- The affine composition square as an equality of its specified isomorphisms. -/
theorem composition (f : R ⟶ S) (g : S ⟶ T) :
    (tilde.functor T).mapIso ((ModuleCat.extendScalarsComp f.hom g.hom).app M).symm ≪≫
      Gluing.comparison M e (f ≫ g) =
    Gluing.comparison ((ModuleCat.extendScalars f.hom).obj M) (Gluing.comparison M e f) g ≪≫
      (Composition.geometricCompositionIso f g).app L := by
  apply Iso.ext
  exact ComparisonCongr.comparison_composition M e f g

/-- Equality of coordinate maps as an equality of the affine presentation isomorphisms. -/
theorem congr {f g : R ⟶ S} (h : f = g) :
    (tilde.functor S).mapIso
        (eqToIso (congrArg (fun r : R ⟶ S => (ModuleCat.extendScalars r.hom).obj M) h)) ≪≫
      Gluing.comparison M e g =
    Gluing.comparison M e f ≪≫ (Scheme.Modules.pullbackCongr (congrArg Spec.map h)).app L := by
  subst g
  change (tilde.functor S).mapIso (Iso.refl _) ≪≫ Gluing.comparison M e f =
    Gluing.comparison M e f ≪≫ Iso.refl _
  simp only [Functor.mapIso_refl, Iso.refl_trans, Iso.trans_refl]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.ComparisonIsos
