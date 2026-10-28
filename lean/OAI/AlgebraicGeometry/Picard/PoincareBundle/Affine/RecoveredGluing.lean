import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CanonicalGluing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.GluingMorphismTransfer

/-! # Recovered Gluing -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.RecoveredGluing

noncomputable section

/-!
# Recover geometric gluing from a compatible affine module comparison
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Gluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PresentedMorphisms OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CanonicalGluing
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.GluingMorphismTransfer

variable {R S T : CommRingCat.{u}} (f : R ⟶ S) (i j : S ⟶ T) (h : f ≫ i = f ≫ j)
  (A : ModuleCat.{u} R) {L : (Spec R).Modules} (eA : (tilde.functor R).obj A ≅ L)
  (N : ModuleCat.{u} S) {K : (Spec S).Modules} (eN : (tilde.functor S).obj N ≅ K)
  (a : (ModuleCat.extendScalars f.hom).obj A ⟶ N)
  (τ : (Scheme.Modules.pullback (Spec.map i)).obj K ⟶
    (Scheme.Modules.pullback (Spec.map j)).obj K)

/-- A compatible comparison of modules gives a compatible comparison of their geometric sheaves. -/
theorem transfer_from_base
    (ha : (ModuleCat.extendScalars i.hom).map a ≫ Gluing.moduleHom N eN i j τ =
      (CanonicalGluing.moduleTransition f i j h A).hom ≫ (ModuleCat.extendScalars j.hom).map a) :
    GluingMorphismTransfer.PreservesGeometricGluing i j (PresentedMorphisms.presentedMap (Gluing.comparison A eA f) eN a)
      ((CanonicalGluing.geometricTransition f i j h).hom.app L) τ :=
  GluingMorphismTransfer.transfer i j (Gluing.comparison A eA f) eN a
    (CanonicalGluing.moduleTransition f i j h A).hom (Gluing.moduleHom N eN i j τ)
    ((CanonicalGluing.geometricTransition f i j h).hom.app L) τ
    (CanonicalGluing.comparison_square f i j h A eA) (PresentedMorphisms.moduleHom_square N eN i j τ) ha

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.RecoveredGluing
