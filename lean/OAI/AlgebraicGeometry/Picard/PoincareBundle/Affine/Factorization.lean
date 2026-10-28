import OAI.AlgebraicGeometry.Picard.PoincareBundle.PresentedMapComposition

/-! # Factorization -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Factorization

noncomputable section

/-!
# Factorization through an affine recovery map can be checked on modules
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Gluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PresentedMorphisms

variable {R S : CommRingCat.{u}} (f : R ⟶ S)
  {M N : ModuleCat.{u} R} {P : ModuleCat.{u} S}
  {X Y : (Spec R).Modules} {Z : (Spec S).Modules}
  (eM : (tilde.functor R).obj M ≅ X) (eN : (tilde.functor R).obj N ≅ Y)
  (eP : (tilde.functor S).obj P ≅ Z)
  (b : M ⟶ N) (c : (ModuleCat.extendScalars f.hom).obj N ⟶ P)

/-- The composite geometric map is the presentation of the composite module map. -/
theorem composite_eq :
    (Scheme.Modules.pullback (Spec.map f)).map (PresentedMorphisms.presentedMap eM eN b) ≫
      PresentedMorphisms.presentedMap (Gluing.comparison N eN f) eP c =
    PresentedMorphisms.presentedMap (Gluing.comparison M eM f) eP ((ModuleCat.extendScalars f.hom).map b ≫ c) := by
  have hp := PresentedMapComposition.pullback_presentedMap f eM eN b
  have hc := PresentedMapComposition.composition (tilde.functor S)
    (Gluing.comparison M eM f) (Gluing.comparison N eN f) eP ((ModuleCat.extendScalars f.hom).map b) c
  exact (congrArg (fun z => z ≫ PresentedMorphisms.presentedMap (Gluing.comparison N eN f) eP c) hp.symm).trans hc

/-- Factorization of the actual geometric maps is equivalent to factorization of their modules. -/
theorem factorization_iff (a : (ModuleCat.extendScalars f.hom).obj M ⟶ P) :
    ((Scheme.Modules.pullback (Spec.map f)).map (PresentedMorphisms.presentedMap eM eN b) ≫
      PresentedMorphisms.presentedMap (Gluing.comparison N eN f) eP c = PresentedMorphisms.presentedMap (Gluing.comparison M eM f) eP a) ↔
    (ModuleCat.extendScalars f.hom).map b ≫ c = a := by
  constructor
  · intro h
    apply PresentedMapComposition.injective (tilde.functor S) (Gluing.comparison M eM f) eP
    exact (composite_eq f eM eN eP b c).symm.trans h
  · intro h
    exact (composite_eq f eM eN eP b c).trans
      (congrArg (PresentedMorphisms.presentedMap (Gluing.comparison M eM f) eP) h)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Factorization
