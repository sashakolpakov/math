import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechRecovery
import OAI.AlgebraicGeometry.Picard.PoincareBundle.GluingReflection
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PresentedMapFullness
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.NaturalGluingCompatibility

/-! # Cech Morphism Coordinates -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechMorphismCoordinates

noncomputable section

/-!
# The exact module map underlying a geometric Čech-compatible morphism
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.ModuleCat

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Gluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PresentedMorphisms OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.GluingMorphismTransfer
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CanonicalGluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechCanonicalCoordinates OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechRecovery

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (D : CocycleDescent.RingMapDatum f)
  {P : (Spec R).Modules} (φ : (Scheme.Modules.pullback (Spec.map f)).obj P ⟶ (CechRecovery.originalLine f D).sheaf)

/-- Compatibility with the original Čech gluing, using the standard geometric pullback maps. -/
def Compatible : Prop :=
  letI := f.hom.toAlgebra
  Affine.NaturalGluingCompatibility.CompatibleWith f (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f) φ
    D.gluing.hom
    (Cech.MateNormalization.standardGluing (Spec.map f) (Spec.map (Affine.CechCanonicalCoordinates.firstProjection f))
      (Spec.map (Affine.CechCanonicalCoordinates.secondProjection f))
      (Affine.CanonicalGluingStandard.projection_eq f (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f)
        (Affine.CechCanonicalCoordinates.baseEquation f)))

/-- The same compatibility in the canonical affine composition coordinates. -/
def GeometricCompatible : Prop :=
  letI := f.hom.toAlgebra
  Affine.NaturalGluingCompatibility.CompatibleWith f (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f) φ
    D.gluing.hom (Affine.CanonicalGluing.geometricTransition f (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f) (Affine.CechCanonicalCoordinates.baseEquation f))

theorem compatible_geometric (hφ : Compatible f D φ) : GeometricCompatible f D φ := by
  let := f.hom.toAlgebra
  exact (Affine.NaturalGluingCompatibility.congr f (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f) φ
    D.gluing.hom (Affine.CanonicalGluingStandard.geometricTransition_eq_standard f
      (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f) (Affine.CechCanonicalCoordinates.baseEquation f))).mpr hφ

variable (A : ModuleCat.{u} R) (eP : (tilde.functor R).obj A ≅ P)

/-- The actual scalar-extended module map underlying the geometric morphism. -/
def moduleMap : (extendScalars f.hom).obj A ⟶ CechRecovery.sectionModule f D :=
  Affine.PresentedMapFullness.moduleMap (Affine.Gluing.comparison A eP f) (CechRecovery.presentation f D) φ

theorem moduleMap_presented :
    Affine.PresentedMorphisms.presentedMap (Affine.Gluing.comparison A eP f) (CechRecovery.presentation f D) (moduleMap f D φ A eP) = φ :=
  Affine.PresentedMapFullness.presentedMap_moduleMap (Affine.Gluing.comparison A eP f) (CechRecovery.presentation f D) φ

/-- The original geometric compatibility becomes precisely the original module Čech compatibility. -/
theorem moduleMap_preservesGluing (hφ : Compatible f D φ) :
    letI := f.hom.toAlgebra
    Cech.GluingMorphisms.PreservesGluing R S (moduleMap f D φ A eP)
      (Canonical.CechCoaction.datum f.hom A) (CechRecovery.moduleCech f D) := by
  let := f.hom.toAlgebra
  have hp : Affine.GluingMorphismTransfer.PreservesGeometricGluing (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f)
      (Affine.PresentedMorphisms.presentedMap (Affine.Gluing.comparison A eP f) (CechRecovery.presentation f D) (moduleMap f D φ A eP))
      ((Affine.CanonicalGluing.geometricTransition f (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f) (Affine.CechCanonicalCoordinates.baseEquation f)).hom.app P)
      D.gluing.hom := by
    rw [moduleMap_presented]
    exact compatible_geometric f D φ hφ
  have hm := GluingReflection.affine_reflect (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f)
    (Affine.Gluing.comparison A eP f) (CechRecovery.presentation f D) (moduleMap f D φ A eP)
    (Affine.CanonicalGluing.moduleTransition f (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f) (Affine.CechCanonicalCoordinates.baseEquation f) A).hom
    (Affine.Gluing.moduleHom (CechRecovery.sectionModule f D) (CechRecovery.presentation f D) (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f)
      D.gluing.hom)
    ((Affine.CanonicalGluing.geometricTransition f (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f) (Affine.CechCanonicalCoordinates.baseEquation f)).hom.app P)
    D.gluing.hom (Affine.CanonicalGluing.comparison_square f (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f) (Affine.CechCanonicalCoordinates.baseEquation f) A eP)
    (Affine.PresentedMorphisms.moduleHom_square (CechRecovery.sectionModule f D) (CechRecovery.presentation f D) (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f)
      D.gluing.hom) hp
  rw [Affine.CechCanonicalCoordinates.moduleTransition_eq_canonical, ← CechRecovery.moduleCech_gluing_hom] at hm
  exact hm

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechMorphismCoordinates
