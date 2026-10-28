import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechMorphismCoordinates
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Cech.MorphismDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Factorization

/-! # Cech Morphism Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechMorphismDescent

noncomputable section

/-!
# Effective descent of ordinary geometric Čech-compatible morphisms
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.ModuleCat

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Gluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PresentedMorphisms OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechRecovery
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechMorphismCoordinates

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (D : CocycleDescent.RingMapDatum f)
  {P : (Spec R).Modules} (φ : (Scheme.Modules.pullback (Spec.map f)).obj P ⟶ (CechRecovery.originalLine f D).sheaf)
  (A : ModuleCat.{u} R) (eP : (tilde.functor R).obj A ≅ P)
  (hφ : CechMorphismCoordinates.Compatible f D φ) (hf : f.hom.FaithfullyFlat)

/-- The actual descended module morphism associated to the geometric compatible map. -/
def moduleLift : A ⟶ CechRecovery.baseModule f D hf :=
  Cech.MorphismDescent.lift f.hom A (CechRecovery.sectionModule f D) (CechRecovery.moduleCech f D)
    (CechMorphismCoordinates.moduleMap f D φ A eP) (CechMorphismCoordinates.moduleMap_preservesGluing f D φ A eP hφ) hf

theorem moduleLift_fac :
    (extendScalars f.hom).map (moduleLift f D φ A eP hφ hf) ≫ (CechRecovery.moduleRecoveryIso f D hf).hom =
      CechMorphismCoordinates.moduleMap f D φ A eP :=
  Cech.MorphismDescent.lift_fac f.hom A (CechRecovery.sectionModule f D) (CechRecovery.moduleCech f D)
    (CechMorphismCoordinates.moduleMap f D φ A eP) (CechMorphismCoordinates.moduleMap_preservesGluing f D φ A eP hφ) hf

/-- The descended morphism between the actual geometric sheaves. -/
def lift : P ⟶ (tilde.functor R).obj (CechRecovery.baseModule f D hf) :=
  Affine.PresentedMorphisms.presentedMap eP (Iso.refl _) (moduleLift f D φ A eP hφ hf)

/-- Pullback through the recovered bundle gives exactly the original geometric compatible map. -/
theorem lift_fac :
    (Scheme.Modules.pullback (Spec.map f)).map (lift f D φ A eP hφ hf) ≫
      (CechRecovery.recoveryIso f D hf).hom = φ := by
  have hm := (Affine.Factorization.factorization_iff f eP (Iso.refl _) (CechRecovery.presentation f D)
    (moduleLift f D φ A eP hφ hf) (CechRecovery.moduleRecoveryIso f D hf).hom (CechMorphismCoordinates.moduleMap f D φ A eP)).mpr
      (moduleLift_fac f D φ A eP hφ hf)
  have he := congrArg (fun z =>
    (Scheme.Modules.pullback (Spec.map f)).map (lift f D φ A eP hφ hf) ≫ z)
    (CechRecovery.recoveryIso_hom f D hf)
  exact he.trans (hm.trans (CechMorphismCoordinates.moduleMap_presented f D φ A eP))

/-- The descended geometric morphism is uniquely determined by the supplied compatible map. -/
theorem lift_unique (b : P ⟶ (tilde.functor R).obj (CechRecovery.baseModule f D hf))
    (hb : (Scheme.Modules.pullback (Spec.map f)).map b ≫ (CechRecovery.recoveryIso f D hf).hom = φ) :
    b = lift f D φ A eP hφ hf := by
  let bM := Affine.PresentedMapFullness.moduleMap eP (Iso.refl _) b
  have hp := Affine.PresentedMapFullness.presentedMap_moduleMap eP (Iso.refl _) b
  have hgeom := (congrArg (fun z => (Scheme.Modules.pullback (Spec.map f)).map z ≫
    Affine.PresentedMorphisms.presentedMap (Affine.Gluing.comparison (CechRecovery.baseModule f D hf) (Iso.refl _) f) (CechRecovery.presentation f D)
      (CechRecovery.moduleRecoveryIso f D hf).hom) hp).trans
    ((congrArg (fun z => (Scheme.Modules.pullback (Spec.map f)).map b ≫ z)
      (CechRecovery.recoveryIso_hom f D hf).symm).trans (hb.trans (CechMorphismCoordinates.moduleMap_presented f D φ A eP).symm))
  have hmod := (Affine.Factorization.factorization_iff f eP (Iso.refl _) (CechRecovery.presentation f D)
    bM (CechRecovery.moduleRecoveryIso f D hf).hom (CechMorphismCoordinates.moduleMap f D φ A eP)).mp hgeom
  have hu := Cech.MorphismDescent.lift_unique f.hom A (CechRecovery.sectionModule f D) (CechRecovery.moduleCech f D)
    (CechMorphismCoordinates.moduleMap f D φ A eP) (CechMorphismCoordinates.moduleMap_preservesGluing f D φ A eP hφ) hf bM hmod
  exact hp.symm.trans (congrArg (Affine.PresentedMorphisms.presentedMap eP (Iso.refl _)) hu)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechMorphismDescent
