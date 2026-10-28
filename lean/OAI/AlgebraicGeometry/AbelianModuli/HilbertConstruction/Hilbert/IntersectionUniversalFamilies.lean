import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyTestPoints

/-! # Intersection Universal Families -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.IntersectionUniversalFamilies

noncomputable section

/-! The two actual universal families restricted to a Hilbert
intersection have canonical transports on every Noetherian affine
test. Their total spaces are locally Noetherian over a Noetherian base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

instance nativeFamilyOver_locallyNoetherian {S : Scheme.{u}} (X T : Over S)
    [IsLocallyNoetherian T.left] (F : HilbertScheme.Presentations.Hilbert.Functor.Family X T) :
    IsLocallyNoetherian (Intrinsic.FamilyTestPoints.nativeFamilyOver X T F).left := by
  have : LocallyOfFinitePresentation (HilbertScheme.Presentations.Hilbert.Functor.familyProjection X F.val) := F.property.2.2
  have : LocallyOfFiniteType (HilbertScheme.Presentations.Hilbert.Functor.familyProjection X F.val) :=
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mp inferInstance
  exact LocallyOfFiniteType.isLocallyNoetherian (HilbertScheme.Presentations.Hilbert.Functor.familyProjection X F.val)

private theorem nativeAffineFamilyTransport_of_eq
    {S : Scheme.{u}} {C : Type u} [CommRing C] (n : ℕ) (f : Spec (.of C) ⟶ S)
    (F F' G G' : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f))
    (E : HilbertScheme.Presentations.Hilbert.Functor.ambient (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f) ⟶
      HilbertScheme.Presentations.Hilbert.Functor.ambient (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f))
    (hF : F = F') (hG : G = G')
    (h : ∃! e : Intrinsic.AffineFamilyTransport.affineNativeFamilyOver n f F' ≅ Intrinsic.AffineFamilyTransport.affineNativeFamilyOver n f G',
      e.hom.left ≫ G'.val.subschemeι = F'.val.subschemeι ≫ E) :
    ∃! e : Intrinsic.FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f) F ≅
      Intrinsic.FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk f) G,
      e.hom.left ≫ G.val.subschemeι = F.val.subschemeι ≫ E := by
  cases hF
  cases hG
  exact h

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (D : ℕ) (P : Polynomial ℚ)
variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)

def hilbertIntersectionLeftFamily :
    HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
      (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P) :=
  HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
    (StableHilbert.IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)
    (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P)

def hilbertIntersectionRightFamily :
    HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
      (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P) :=
  HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
    (StableHilbert.IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD)
    (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i k D P)

variable (C : CommRingCat.{u}) [IsNoetherianRing C]
variable {f : Spec C ⟶ Spec (.of R)}
variable (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)

omit [IsNoetherianRing C] in
theorem hilbertIntersectionLeftFamily_affine :
    HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
      (hilbertIntersectionLeftFamily R i j k D P hP hD) =
    StableHilbert.AffineFamily.stableHilbertAffineFamily R C i j D P (a ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD) := by
  exact (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily_comp _ _ _ _).symm.trans
    (StableHilbert.AffineFamily.stableHilbertAffineFamily_pullback R C i j D P
      (a ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)).symm

omit [IsNoetherianRing C] in
theorem hilbertIntersectionRightFamily_affine :
    HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
      (hilbertIntersectionRightFamily R i j k D P hP hD) =
    StableHilbert.AffineFamily.stableHilbertAffineFamily R C i k D P (a ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD) := by
  exact (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily_comp _ _ _ _).symm.trans
    (StableHilbert.AffineFamily.stableHilbertAffineFamily_pullback R C i k D P
      (a ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD)).symm

theorem hilbertIntersectionAffineTransport_existsUnique :
    let X := HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n
    let F := HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a (hilbertIntersectionLeftFamily R i j k D P hP hD)
    let G := HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a (hilbertIntersectionRightFamily R i j k D P hP hD)
    let E := StableProjectiveTransport.rawStableIntersectionProjectiveIso R i j k
      (a ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D P)
    ∃! e : Intrinsic.FamilyTestPoints.nativeFamilyOver X (Over.mk f) F ≅ Intrinsic.FamilyTestPoints.nativeFamilyOver X (Over.mk f) G,
      e.hom.left ≫ G.val.subschemeι = F.val.subschemeι ≫ Intrinsic.AffineTransportNaturality.affineNativeAmbientTransport n f E := by
  cases C with
  | of C =>
    let X := HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n
    let F := HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a (hilbertIntersectionLeftFamily R i j k D P hP hD)
    let G := HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a (hilbertIntersectionRightFamily R i j k D P hP hD)
    let F' := StableHilbert.AffineFamily.stableHilbertAffineFamily R (.of C) i j D P
      (a ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)
    let G' := StableHilbert.AffineFamily.stableHilbertAffineFamily R (.of C) i k D P
      (a ≫ StableHilbert.IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD)
    let E := Intrinsic.AffineTransportNaturality.affineNativeAmbientTransport n f (StableProjectiveTransport.rawStableIntersectionProjectiveIso R i j k
      (a ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D P))
    have hF : F = F' := hilbertIntersectionLeftFamily_affine R i j k D P hP hD (.of C) a
    have hG : G = G' := hilbertIntersectionRightFamily_affine R i j k D P hP hD (.of C) a
    have h := IntrinsicTransport.rawHilbertNativeTransport_existsUnique R i j k D P hP hD a
    exact nativeAffineFamilyTransport_of_eq n f F F' G G' E hF hG h

def hilbertIntersectionAffineTransport :
    Intrinsic.FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) (Over.mk f)
      (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
        (hilbertIntersectionLeftFamily R i j k D P hP hD)) ≅
    Intrinsic.FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) (Over.mk f)
      (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
        (hilbertIntersectionRightFamily R i j k D P hP hD)) :=
  (hilbertIntersectionAffineTransport_existsUnique R i j k D P hP hD C a).choose

theorem hilbertIntersectionAffineTransport_ambient :
    (hilbertIntersectionAffineTransport R i j k D P hP hD C a).hom.left ≫
      (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
        (hilbertIntersectionRightFamily R i j k D P hP hD)).val.subschemeι =
    (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
      (hilbertIntersectionLeftFamily R i j k D P hP hD)).val.subschemeι ≫
      Intrinsic.AffineTransportNaturality.affineNativeAmbientTransport n f (StableProjectiveTransport.rawStableIntersectionProjectiveIso R i j k
        (a ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D P)) :=
  (hilbertIntersectionAffineTransport_existsUnique R i j k D P hP hD C a).choose_spec.1

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.IntersectionUniversalFamilies
