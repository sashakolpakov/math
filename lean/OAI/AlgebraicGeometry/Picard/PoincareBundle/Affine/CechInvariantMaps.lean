import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechMorphismCoordinates
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechInvariantQuasiCoherent
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.QCPresentation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.InvariantUniversal

/-! # Cech Invariant Maps -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechInvariantMaps

noncomputable section

/-!
# Maps to and from the actual affine Čech invariant sheaf
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.ModuleCat

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechCanonicalCoordinates OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechRecovery
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechMorphismCoordinates

variable {R S : CommRingCat.{u}} (f : R ⟶ S) (D : Geometric.CocycleDescent.RingMapDatum f)

/-- The actual equalizer invariant sheaf in the affine Čech coordinates. -/
def invariant : (Spec R).Modules := by
  letI := f.hom.toAlgebra
  exact InvariantUniversal.Raw.invariant f (CechCanonicalCoordinates.firstProjection f) (CechCanonicalCoordinates.secondProjection f)
    (CanonicalGluingStandard.projection_eq f (CechCanonicalCoordinates.firstProjection f) (CechCanonicalCoordinates.secondProjection f)
      (CechCanonicalCoordinates.baseEquation f)) (Geometric.CechRecovery.originalLine f D).sheaf D.gluing

/-- Its canonical pullback comparison with the original line bundle. -/
def comparison : (Scheme.Modules.pullback (Spec.map f)).obj (invariant f D) ⟶
    (Geometric.CechRecovery.originalLine f D).sheaf := by
  letI := f.hom.toAlgebra
  exact InvariantUniversal.Raw.comparison f (CechCanonicalCoordinates.firstProjection f) (CechCanonicalCoordinates.secondProjection f)
    (CanonicalGluingStandard.projection_eq f (CechCanonicalCoordinates.firstProjection f) (CechCanonicalCoordinates.secondProjection f)
      (CechCanonicalCoordinates.baseEquation f)) (Geometric.CechRecovery.originalLine f D).sheaf D.gluing

/-- The raw invariant is quasi-coherent, before any effectiveness is claimed. -/
theorem invariant_isQuasicoherent : (invariant f D).IsQuasicoherent := by
  let := f.hom.toAlgebra
  have : (Geometric.CechRecovery.originalLine f D).sheaf.IsQuasicoherent :=
    QuasiCoherent.isQuasicoherent_of_isLine _ (Geometric.CechRecovery.originalLine f D).isLine
  exact CechInvariantQuasiCoherent.invariantSheaf_isQuasicoherent f
    (CechCanonicalCoordinates.firstProjection f) (CechCanonicalCoordinates.secondProjection f)
    (CanonicalGluingStandard.projection_eq f (CechCanonicalCoordinates.firstProjection f) (CechCanonicalCoordinates.secondProjection f)
      (CechCanonicalCoordinates.baseEquation f)) (Geometric.CechRecovery.originalLine f D).sheaf D.gluing

/-- The invariant's actual global-section module. -/
def invariantModule : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj (invariant f D)

def invariantPresentation : (tilde.functor R).obj (invariantModule f D) ≅ invariant f D := by
  have := invariant_isQuasicoherent f D
  exact QCPresentation.presentation (invariant f D)

/-- The invariant comparison respects the original standard geometric Čech gluing. -/
theorem comparison_compatible : Geometric.CechMorphismCoordinates.Compatible f D (comparison f D) := by
  let := f.hom.toAlgebra
  exact InvariantUniversal.Raw.comparison_compatible f (CechCanonicalCoordinates.firstProjection f) (CechCanonicalCoordinates.secondProjection f)
    (CanonicalGluingStandard.projection_eq f (CechCanonicalCoordinates.firstProjection f) (CechCanonicalCoordinates.secondProjection f)
      (CechCanonicalCoordinates.baseEquation f)) (Geometric.CechRecovery.originalLine f D).sheaf D.gluing

variable {P : (Spec R).Modules}
  (φ : (Scheme.Modules.pullback (Spec.map f)).obj P ⟶ (Geometric.CechRecovery.originalLine f D).sheaf)

/-- Every compatible geometric map has its canonical factor through the actual invariant sheaf. -/
def liftToInvariant (hφ : Geometric.CechMorphismCoordinates.Compatible f D φ) : P ⟶ invariant f D := by
  letI := f.hom.toAlgebra
  exact InvariantUniversal.Raw.lift f (CechCanonicalCoordinates.firstProjection f) (CechCanonicalCoordinates.secondProjection f)
    (CanonicalGluingStandard.projection_eq f (CechCanonicalCoordinates.firstProjection f) (CechCanonicalCoordinates.secondProjection f)
      (CechCanonicalCoordinates.baseEquation f)) (Geometric.CechRecovery.originalLine f D).sheaf D.gluing φ hφ

theorem liftToInvariant_fac (hφ : Geometric.CechMorphismCoordinates.Compatible f D φ) :
    (Scheme.Modules.pullback (Spec.map f)).map (liftToInvariant f D φ hφ) ≫ comparison f D = φ := by
  let := f.hom.toAlgebra
  exact InvariantUniversal.Raw.lift_fac f (CechCanonicalCoordinates.firstProjection f) (CechCanonicalCoordinates.secondProjection f)
    (CanonicalGluingStandard.projection_eq f (CechCanonicalCoordinates.firstProjection f) (CechCanonicalCoordinates.secondProjection f)
      (CechCanonicalCoordinates.baseEquation f)) (Geometric.CechRecovery.originalLine f D).sheaf D.gluing φ hφ

theorem liftToInvariant_unique (hφ : Geometric.CechMorphismCoordinates.Compatible f D φ) (a b : P ⟶ invariant f D)
    (ha : (Scheme.Modules.pullback (Spec.map f)).map a ≫ comparison f D = φ)
    (hb : (Scheme.Modules.pullback (Spec.map f)).map b ≫ comparison f D = φ) : a = b := by
  let := f.hom.toAlgebra
  exact InvariantUniversal.Raw.lift_unique f (CechCanonicalCoordinates.firstProjection f) (CechCanonicalCoordinates.secondProjection f)
    (CanonicalGluingStandard.projection_eq f (CechCanonicalCoordinates.firstProjection f) (CechCanonicalCoordinates.secondProjection f)
      (CechCanonicalCoordinates.baseEquation f)) (Geometric.CechRecovery.originalLine f D).sheaf D.gluing φ hφ a b ha hb

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechInvariantMaps
