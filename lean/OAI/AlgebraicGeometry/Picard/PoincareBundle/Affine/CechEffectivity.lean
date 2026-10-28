import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechInvariantMaps
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechMorphismDescent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.RecoveryComparison

/-! # Cech Effectivity -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechEffectivity

noncomputable section

/-!
# The actual affine Čech invariant sheaf effectively descends the geometric line bundle
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.ModuleCat

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechRecovery OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechMorphismCoordinates
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechInvariantMaps

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (D : Geometric.CocycleDescent.RingMapDatum f)
  (hf : f.hom.FaithfullyFlat)

/-- The already recovered bundle's comparison has the original geometric compatibility. -/
theorem recovery_compatible :
    Geometric.CechMorphismCoordinates.Compatible f D (P := (tilde.functor R).obj (Geometric.CechRecovery.baseModule f D hf)) (Geometric.CechRecovery.recoveryIso f D hf).hom := by
  let := f.hom.toAlgebra
  exact NaturalGluingCompatibility.of_equation f
    (CechCanonicalCoordinates.firstProjection f)
    (CechCanonicalCoordinates.secondProjection f)
    (P := (tilde.functor R).obj (Geometric.CechRecovery.baseModule f D hf)) (M := (Geometric.CechRecovery.originalLine f D).sheaf)
    (Geometric.CechRecovery.recoveryIso f D hf).hom D.gluing.hom
    (Cech.MateNormalization.standardGluing (Spec.map f)
      (Spec.map (CechCanonicalCoordinates.firstProjection f))
      (Spec.map (CechCanonicalCoordinates.secondProjection f))
      (CanonicalGluingStandard.projection_eq f
        (CechCanonicalCoordinates.firstProjection f)
        (CechCanonicalCoordinates.secondProjection f)
        (CechCanonicalCoordinates.baseEquation f))) (Geometric.CechRecovery.recovery_standard_compatible f D hf)

/-- The descended module sheaf maps canonically into the raw invariant sheaf. -/
def toInvariant : (tilde.functor R).obj (Geometric.CechRecovery.baseModule f D hf) ⟶ CechInvariantMaps.invariant f D :=
  CechInvariantMaps.liftToInvariant f D (Geometric.CechRecovery.recoveryIso f D hf).hom (recovery_compatible f D hf)

theorem toInvariant_fac :
    (Scheme.Modules.pullback (Spec.map f)).map (toInvariant f D hf) ≫ CechInvariantMaps.comparison f D =
      (Geometric.CechRecovery.recoveryIso f D hf).hom :=
  CechInvariantMaps.liftToInvariant_fac f D (Geometric.CechRecovery.recoveryIso f D hf).hom (recovery_compatible f D hf)

/-- Descent of the invariant comparison gives the inverse candidate on actual sheaves. -/
def fromInvariant : CechInvariantMaps.invariant f D ⟶ (tilde.functor R).obj (Geometric.CechRecovery.baseModule f D hf) :=
  Geometric.CechMorphismDescent.lift f D (CechInvariantMaps.comparison f D)
    (CechInvariantMaps.invariantModule f D) (CechInvariantMaps.invariantPresentation f D) (CechInvariantMaps.comparison_compatible f D) hf

theorem fromInvariant_fac :
    (Scheme.Modules.pullback (Spec.map f)).map (fromInvariant f D hf) ≫
      (Geometric.CechRecovery.recoveryIso f D hf).hom = CechInvariantMaps.comparison f D :=
  Geometric.CechMorphismDescent.lift_fac f D (CechInvariantMaps.comparison f D)
    (CechInvariantMaps.invariantModule f D) (CechInvariantMaps.invariantPresentation f D) (CechInvariantMaps.comparison_compatible f D) hf

/-- Uniqueness of descended geometric morphisms detects the identity on the recovered bundle. -/
theorem recovered_endomorphism_unique
    (a : (tilde.functor R).obj (Geometric.CechRecovery.baseModule f D hf) ⟶ (tilde.functor R).obj (Geometric.CechRecovery.baseModule f D hf))
    (ha : (Scheme.Modules.pullback (Spec.map f)).map a ≫ (Geometric.CechRecovery.recoveryIso f D hf).hom =
      (Geometric.CechRecovery.recoveryIso f D hf).hom) : a = 𝟙 _ := by
  have hi : (Scheme.Modules.pullback (Spec.map f)).map (𝟙 ((tilde.functor R).obj (Geometric.CechRecovery.baseModule f D hf))) ≫
      (Geometric.CechRecovery.recoveryIso f D hf).hom = (Geometric.CechRecovery.recoveryIso f D hf).hom := by
    rw [(Scheme.Modules.pullback (Spec.map f)).map_id, Category.id_comp]
  exact (Geometric.CechMorphismDescent.lift_unique f D (Geometric.CechRecovery.recoveryIso f D hf).hom
    (Geometric.CechRecovery.baseModule f D hf) (Iso.refl _) (recovery_compatible f D hf) hf a ha).trans
      (Geometric.CechMorphismDescent.lift_unique f D (Geometric.CechRecovery.recoveryIso f D hf).hom
        (Geometric.CechRecovery.baseModule f D hf) (Iso.refl _) (recovery_compatible f D hf) hf (𝟙 _) hi).symm

/-- The invariant universal property detects the identity on the actual equalizer sheaf. -/
theorem invariant_endomorphism_unique (a : CechInvariantMaps.invariant f D ⟶ CechInvariantMaps.invariant f D)
    (ha : (Scheme.Modules.pullback (Spec.map f)).map a ≫ CechInvariantMaps.comparison f D = CechInvariantMaps.comparison f D) :
    a = 𝟙 _ := by
  apply CechInvariantMaps.liftToInvariant_unique f D (CechInvariantMaps.comparison f D) (CechInvariantMaps.comparison_compatible f D) a (𝟙 _) ha
  rw [(Scheme.Modules.pullback (Spec.map f)).map_id, Category.id_comp]

/-- The raw Čech invariant sheaf is the sheaf constructed by effective affine descent. -/
def invariantIso : (tilde.functor R).obj (Geometric.CechRecovery.baseModule f D hf) ≅ CechInvariantMaps.invariant f D :=
  RecoveryComparison.recoveryIso (Scheme.Modules.pullback (Spec.map f))
    (Geometric.CechRecovery.recoveryIso f D hf) (CechInvariantMaps.comparison f D) (toInvariant f D hf) (fromInvariant f D hf)
    (toInvariant_fac f D hf) (fromInvariant_fac f D hf)
    (recovered_endomorphism_unique f D hf) (invariant_endomorphism_unique f D)

include hf in
/-- The actual canonical Čech invariant comparison is an isomorphism. -/
theorem comparison_isIso : IsIso (CechInvariantMaps.comparison f D) :=
  RecoveryComparison.comparison_isIso (Scheme.Modules.pullback (Spec.map f))
    (Geometric.CechRecovery.recoveryIso f D hf) (CechInvariantMaps.comparison f D) (toInvariant f D hf) (fromInvariant f D hf)
    (toInvariant_fac f D hf) (fromInvariant_fac f D hf)
    (recovered_endomorphism_unique f D hf) (invariant_endomorphism_unique f D)

include hf in
/-- Over a noetherian affine base, the actual invariant equalizer is itself a line bundle. -/
theorem invariant_isLine [IsNoetherianRing R] : Line.Bundles.IsLine (CechInvariantMaps.invariant f D) := by
  have := Geometric.CechRecovery.baseModule_invertible f D hf
  exact (TildePullback.isLine_tilde_of_invertible (Geometric.CechRecovery.baseModule f D hf)).of_iso (invariantIso f D hf)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechEffectivity
