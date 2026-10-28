import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.IntersectionUniversalFamilies
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.AmbientTransportOverNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyPointNaturality

/-! # Intersection Point Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.IntersectionPointNaturality

noncomputable section

/-! The actual family transports on a stable Hilbert intersection
give natural equivalences of affine test points. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private def hilbertTestRestriction {S : Scheme.{u}} {T U V : Over S}
    (a : U ⟶ T) (b : V ⟶ U) : Over.mk (b ≫ a).left ⟶ Over.mk a.left :=
  Over.homMk b.left (by rfl)

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (D : ℕ) (P : Polynomial ℚ)
variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
variable (C A : CommRingCat.{u}) [IsNoetherianRing C] [IsNoetherianRing A]
variable {f : Spec C ⟶ Spec (.of R)}
variable (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)

def hilbertIntersectionTestPointEquiv :
    (Over.mk a.left ⟶ Intrinsic.FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
      (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)
      (IntersectionUniversalFamilies.hilbertIntersectionLeftFamily R i j k D P hP hD)) ≃
    (Over.mk a.left ⟶ Intrinsic.FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
      (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)
      (IntersectionUniversalFamilies.hilbertIntersectionRightFamily R i j k D P hP hD)) :=
  Intrinsic.FamilyTestPoints.nativeFamilyTestPointTransport (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a _ _
    (IntersectionUniversalFamilies.hilbertIntersectionAffineTransport R i j k D P hP hD C a)

theorem hilbertIntersectionTestPointEquiv_natural
    (g : Spec A ⟶ Spec (.of R)) (b : Over.mk g ⟶ Over.mk f)
    (x : Over.mk a.left ⟶ Intrinsic.FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
      (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)
      (IntersectionUniversalFamilies.hilbertIntersectionLeftFamily R i j k D P hP hD)) :
    hilbertIntersectionTestPointEquiv R i j k D P hP hD A (b ≫ a) (hilbertTestRestriction a b ≫ x) =
      hilbertTestRestriction a b ≫ hilbertIntersectionTestPointEquiv R i j k D P hP hD C a x := by
  apply Intrinsic.FamilyPointNaturality.nativeFamilyTestPointTransport_natural (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a b _ _
    (IntersectionUniversalFamilies.hilbertIntersectionAffineTransport R i j k D P hP hD C a)
    (IntersectionUniversalFamilies.hilbertIntersectionAffineTransport R i j k D P hP hD A (b ≫ a))
    (Intrinsic.AffineTransportNaturality.affineNativeAmbientTransport n f (StableProjectiveTransport.rawStableIntersectionProjectiveIso R i j k
      (a ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D P)))
    (Intrinsic.AffineTransportNaturality.affineNativeAmbientTransport n g (StableProjectiveTransport.rawStableIntersectionProjectiveIso R i j k
      ((b ≫ a) ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D P)))
    (IntersectionUniversalFamilies.hilbertIntersectionAffineTransport_ambient R i j k D P hP hD C a)
    (IntersectionUniversalFamilies.hilbertIntersectionAffineTransport_ambient R i j k D P hP hD A (b ≫ a))
    ?_ x
  simpa only [Category.assoc] using AmbientTransportOverNaturality.rawStableNativeAmbientTransport_natural R i j k
    (a ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D P) g b

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.IntersectionPointNaturality
