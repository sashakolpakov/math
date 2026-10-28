import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.AffineOverlap
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.OverlapPresentation
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechEffectivity

/-! # Affine Effectivity -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.AffineEffectivity

noncomputable section

/-!
# Effectivity of ordinary descent on the actual affine scheme kernel pair
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.KernelLinearization OAI.AlgebraicGeometry.Picard.PoincareBundle.Geometric.CechInvariant
open OAI.AlgebraicGeometry.Picard.PoincareBundle.Affine.CechCanonicalCoordinates

variable {R S : CommRingCat.{u}} (f : R ⟶ S)
  (D : Geometric.KernelLinearization.modulePullbacks.DescentData (fun (_ : PUnit.{1}) => Spec.map f))
  (hline : Line.Bundles.IsLine (D.obj PUnit.unit))

/-- The tensor-coordinate invariant is canonically the invariant on the actual scheme kernel pair. -/
def invariantIso :
    Affine.CechInvariantMaps.invariant f (AffineDescent.ringMapGeometricDatum f D hline) ≅
      Geometric.CechInvariant.ordinaryInvariantSheaf (Spec.map f) D := by
  letI := f.hom.toAlgebra
  exact Geometric.OverlapPresentation.invariantIso (Spec.map f)
    (pullback.fst (Spec.map f) (Spec.map f)) (pullback.snd (Spec.map f) (Spec.map f))
    pullback.condition (Affine.CechPullback.overlapIso f).inv (D.obj PUnit.unit)
    (Geometric.CechInvariant.relationGluing (Spec.map f) D) (Spec.map (Affine.CechCanonicalCoordinates.firstProjection f)) (Spec.map (Affine.CechCanonicalCoordinates.secondProjection f))
    (Affine.CanonicalGluingStandard.projection_eq f (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f)
      (Affine.CechCanonicalCoordinates.baseEquation f)) (AffineDescent.overlapIso R S D)
    (Affine.CechPullback.overlapIso_inv_fst f) (Affine.CechPullback.overlapIso_inv_snd f)
    (AffineOverlap.tensor_gluing f D)

/-- The coordinate identification retains the actual canonical comparison to the cover. -/
theorem comparison_fac :
    (Scheme.Modules.pullback (Spec.map f)).map (invariantIso f D hline).hom ≫
      Geometric.CechInvariant.ordinaryComparison (Spec.map f) D =
    Affine.CechInvariantMaps.comparison f (AffineDescent.ringMapGeometricDatum f D hline) := by
  let := f.hom.toAlgebra
  exact Geometric.OverlapPresentation.comparison_fac (Spec.map f)
    (pullback.fst (Spec.map f) (Spec.map f)) (pullback.snd (Spec.map f) (Spec.map f))
    pullback.condition (Affine.CechPullback.overlapIso f).inv (D.obj PUnit.unit)
    (Geometric.CechInvariant.relationGluing (Spec.map f) D) (Spec.map (Affine.CechCanonicalCoordinates.firstProjection f)) (Spec.map (Affine.CechCanonicalCoordinates.secondProjection f))
    (Affine.CanonicalGluingStandard.projection_eq f (Affine.CechCanonicalCoordinates.firstProjection f) (Affine.CechCanonicalCoordinates.secondProjection f)
      (Affine.CechCanonicalCoordinates.baseEquation f)) (AffineDescent.overlapIso R S D)
    (Affine.CechPullback.overlapIso_inv_fst f) (Affine.CechPullback.overlapIso_inv_snd f)
    (AffineOverlap.tensor_gluing f D)

include hline in
/-- Faithfully flat affine descent makes the actual ordinary invariant comparison invertible. -/
theorem comparison_isIso (hf : f.hom.FaithfullyFlat) :
    IsIso (Geometric.CechInvariant.ordinaryComparison (Spec.map f) D) := by
  have hi := Affine.CechEffectivity.comparison_isIso f
    (AffineDescent.ringMapGeometricDatum f D hline) hf
  rw [← comparison_fac f D hline] at hi
  exact (isIso_comp_left_iff _ _).mp hi

include hline in
/-- Over a noetherian base, the actual ordinary invariant sheaf is a line bundle. -/
theorem invariant_isLine [IsNoetherianRing R] (hf : f.hom.FaithfullyFlat) :
    Line.Bundles.IsLine (Geometric.CechInvariant.ordinaryInvariantSheaf (Spec.map f) D) :=
  (Affine.CechEffectivity.invariant_isLine f
    (AffineDescent.ringMapGeometricDatum f D hline) hf).of_iso (invariantIso f D hline)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.AffineEffectivity
