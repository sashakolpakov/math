import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.RecoveredGluing
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechCanonicalCoordinates
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CanonicalGluingStandard
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CocycleDescent

/-! # Cech Recovery -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechRecovery

noncomputable section

/-!
# A descended affine line bundle recovers its actual geometric Čech gluing
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.ModuleCat

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.Gluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CanonicalGluing OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechCanonicalCoordinates
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.GluingMorphismTransfer OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.PresentedMorphisms

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (D : CocycleDescent.RingMapDatum f)

/-- The original line bundle, forgetting only the affine scalar-coordinate presentation. -/
def originalLine : Line.Bundles.LineBundle (Spec S) := by
  letI := f.hom.toAlgebra
  exact D.line

/-- The actual global-section module of the original geometric line bundle. -/
def sectionModule : ModuleCat.{u} S := (moduleSpecΓFunctor (R := S)).obj (originalLine f D).sheaf

/-- Its actual Čech cocycle is transferred from the given geometric gluing. -/
def moduleCech : CocycleEffectiveDescent.RingMapDatum f.hom (sectionModule f D) :=
  (CocycleDescent.moduleLineDatum f D).cech

/-- The canonical affine presentation of the original line bundle. -/
def presentation : (tilde.functor S).obj (sectionModule f D) ≅ (originalLine f D).sheaf :=
  QuasiCoherent.affineTildeIso (originalLine f D)

/-- The module obtained by faithfully flat descent. -/
def baseModule (hf : f.hom.FaithfullyFlat) : ModuleCat.{u} R :=
  CocycleEffectiveDescent.descendedModule f.hom (sectionModule f D) hf (moduleCech f D)

/-- The recovered module isomorphism. -/
def moduleRecoveryIso (hf : f.hom.FaithfullyFlat) :
    (extendScalars f.hom).obj (baseModule f D hf) ≅ sectionModule f D :=
  CocycleEffectiveDescent.baseChangeIso f.hom (sectionModule f D) hf (moduleCech f D)

/-- The corresponding actual geometric pullback isomorphism. -/
def recoveryIso (hf : f.hom.FaithfullyFlat) :
    (Scheme.Modules.pullback (Spec.map f)).obj ((tilde.functor R).obj (baseModule f D hf)) ≅
      (originalLine f D).sheaf :=
  PresentedMapNaturality.presentedIso (tilde.functor S)
    (Affine.Gluing.comparison (baseModule f D hf) (Iso.refl _) f) (presentation f D) (moduleRecoveryIso f D hf)

/-- Its sheaf morphism is the affine morphism used by the gluing comparison. -/
theorem recoveryIso_hom (hf : f.hom.FaithfullyFlat) :
    (recoveryIso f D hf).hom = Affine.PresentedMorphisms.presentedMap
      (Affine.Gluing.comparison (baseModule f D hf) (Iso.refl _) f) (presentation f D)
      (moduleRecoveryIso f D hf).hom :=
  PresentedMapNaturality.presentedIso_hom (tilde.functor S)
    (Affine.Gluing.comparison (baseModule f D hf) (Iso.refl _) f) (presentation f D) (moduleRecoveryIso f D hf)

/-- The transferred module gluing is the specific map of the original geometric presentation. -/
theorem moduleCech_gluing_hom :
    letI := f.hom.toAlgebra
    (moduleCech f D).gluing.hom = Affine.Gluing.moduleHom (sectionModule f D) (presentation f D)
      (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f) D.gluing.hom := by
  let := f.hom.toAlgebra
  exact Affine.Gluing.moduleIso_hom (sectionModule f D) (presentation f D)
    (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f) D.gluing

/-- Full module recovery, in the exact coordinates of the original geometric gluing. -/
theorem module_recovery_compatible (hf : f.hom.FaithfullyFlat) :
    letI := f.hom.toAlgebra
    (extendScalars (Affine.CechCanonicalCoordinates.firstProjection f).hom).map (moduleRecoveryIso f D hf).hom ≫
      Affine.Gluing.moduleHom (sectionModule f D) (presentation f D)
        (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f) D.gluing.hom =
    (Affine.CanonicalGluing.moduleTransition f (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f) (Affine.CechCanonicalCoordinates.baseEquation f)
      (baseModule f D hf)).hom ≫
        (extendScalars (Affine.CechCanonicalCoordinates.secondProjection f).hom).map (moduleRecoveryIso f D hf).hom := by
  let := f.hom.toAlgebra
  have ht := Affine.CechCanonicalCoordinates.recovery_compatible f (sectionModule f D) hf (moduleCech f D)
  rw [moduleCech_gluing_hom] at ht
  exact ht

/-- The recovered geometric pullback isomorphism preserves the entire original Čech gluing. -/
theorem recovery_preservesGluing (hf : f.hom.FaithfullyFlat) :
    letI := f.hom.toAlgebra
    Affine.GluingMorphismTransfer.PreservesGeometricGluing (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f) (recoveryIso f D hf).hom
      ((Affine.CanonicalGluing.geometricTransition f (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f) (Affine.CechCanonicalCoordinates.baseEquation f)).hom.app
        ((tilde.functor R).obj (baseModule f D hf))) D.gluing.hom := by
  let := f.hom.toAlgebra
  rw [recoveryIso_hom]
  exact Affine.RecoveredGluing.transfer_from_base f (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f)
    (Affine.CechCanonicalCoordinates.baseEquation f) (baseModule f D hf) (Iso.refl _) (sectionModule f D) (presentation f D)
    (moduleRecoveryIso f D hf).hom D.gluing.hom (module_recovery_compatible f D hf)

/-- Recovery uses the ordinary geometric pullback-composition gluing. -/
theorem recovery_standard_compatible (hf : f.hom.FaithfullyFlat) :
    letI := f.hom.toAlgebra
    Affine.GluingMorphismTransfer.PreservesGeometricGluing (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f) (recoveryIso f D hf).hom
      ((Cech.MateNormalization.standardGluing (Spec.map f) (Spec.map (Affine.CechCanonicalCoordinates.firstProjection f))
        (Spec.map (Affine.CechCanonicalCoordinates.secondProjection f))
        (Affine.CanonicalGluingStandard.projection_eq f (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f)
          (Affine.CechCanonicalCoordinates.baseEquation f))).hom.app ((tilde.functor R).obj (baseModule f D hf))) D.gluing.hom := by
  let := f.hom.toAlgebra
  have he := Affine.CanonicalGluingStandard.geometricTransition_eq_standard f
    (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f) (Affine.CechCanonicalCoordinates.baseEquation f)
  exact Eq.mp (congrArg (fun η =>
    Affine.GluingMorphismTransfer.PreservesGeometricGluing (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f) (recoveryIso f D hf).hom
      (η.hom.app ((tilde.functor R).obj (baseModule f D hf))) D.gluing.hom) he)
    (recovery_preservesGluing f D hf)

/-- The descended module is invertible, since its faithfully flat pullback is the given line. -/
theorem baseModule_invertible [IsNoetherianRing R] (hf : f.hom.FaithfullyFlat) :
    Module.Invertible R (baseModule f D hf) := by
  have : Module.Invertible S
      (CocycleEffectiveDescent.moduleDatum f.hom (sectionModule f D) (moduleCech f D)).A :=
    Affine.Classification.globalSections_invertible (originalLine f D)
  exact Affine.Descent.descendedModule_invertible f.hom hf
    (CocycleEffectiveDescent.moduleDatum f.hom (sectionModule f D) (moduleCech f D))

/-- A genuine descended line bundle whose pullback comparison retains the geometric gluing. -/
def descendedLine [IsNoetherianRing R] (hf : f.hom.FaithfullyFlat) :
    Line.Bundles.LineBundle (Spec R) := by
  have := baseModule_invertible f D hf
  exact TildePullback.lineBundleOfInvertible (baseModule f D hf)

def descendedLinePullbackIso [IsNoetherianRing R] (hf : f.hom.FaithfullyFlat) :
    (Scheme.Modules.pullback (Spec.map f)).obj (descendedLine f D hf).sheaf ≅ (originalLine f D).sheaf :=
  recoveryIso f D hf

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechRecovery
