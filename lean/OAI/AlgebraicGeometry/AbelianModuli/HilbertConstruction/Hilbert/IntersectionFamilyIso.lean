import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.IntersectionPointNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.NoetherianAffineEquivalences

/-! # Intersection Family Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.IntersectionFamilyIso

noncomputable section

/-! The two universal families on an actual stable Hilbert
intersection are isomorphic as schemes over that intersection.
The isomorphism has the canonical formula on every Noetherian affine test. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private def hilbertPointOver {S : Scheme.{u}} (T : Over S) {C : CommRingCat.{u}}
    (f : Spec C ⟶ T.left) : Over.mk (f ≫ T.hom) ⟶ T :=
  Over.homMk f rfl

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m) (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (D : ℕ) (P : Polynomial ℚ)
variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)

def hilbertIntersectionFamilyTestEquiv :
    Relative.NoetherianAffineEquivalences.RelativeNoetherianAffineTestEquiv
      (Intrinsic.FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
        (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)
        (IntersectionUniversalFamilies.hilbertIntersectionLeftFamily R i j k D P hP hD))
      (Intrinsic.FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
        (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)
        (IntersectionUniversalFamilies.hilbertIntersectionRightFamily R i j k D P hP hD)) where
  app := by
    intro C _ f
    exact IntersectionPointNaturality.hilbertIntersectionTestPointEquiv R i j k D P hP hD C (hilbertPointOver (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P) f)
  naturality := by
    intro C A _ _ f g b x
    refine Affine.OverHomInduction.affineOverHom_ring_induction f (fun g b =>
      IntersectionPointNaturality.hilbertIntersectionTestPointEquiv R i j k D P hP hD A (hilbertPointOver (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P) g) (b ≫ x) =
        b ≫ IntersectionPointNaturality.hilbertIntersectionTestPointEquiv R i j k D P hP hD C (hilbertPointOver (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P) f) x) ?_ g b
    intro φ
    let T := Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P
    let a : Over.mk (f ≫ T.hom) ⟶ T := Over.homMk f rfl
    let c : Over.mk ((Spec.map (CommRingCat.ofHom φ) ≫ f) ≫ T.hom) ⟶ Over.mk (f ≫ T.hom) :=
      Over.homMk (Spec.map (CommRingCat.ofHom φ)) (Category.assoc _ _ _).symm
    exact IntersectionPointNaturality.hilbertIntersectionTestPointEquiv_natural R i j k D P hP hD C A a
      ((Spec.map (CommRingCat.ofHom φ) ≫ f) ≫ T.hom) c x

def hilbertIntersectionFamilyIso :
    Intrinsic.FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
      (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)
      (IntersectionUniversalFamilies.hilbertIntersectionLeftFamily R i j k D P hP hD) ≅
    Intrinsic.FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
      (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)
      (IntersectionUniversalFamilies.hilbertIntersectionRightFamily R i j k D P hP hD) :=
  (hilbertIntersectionFamilyTestEquiv R i j k D P hP hD).toIso

theorem hilbertIntersectionFamilyIso_on_affine (C : CommRingCat.{u}) [IsNoetherianRing C]
    (f : Spec C ⟶ (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P).left)
    (x : Over.mk f ⟶ Intrinsic.FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
      (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)
      (IntersectionUniversalFamilies.hilbertIntersectionLeftFamily R i j k D P hP hD)) :
    x ≫ (hilbertIntersectionFamilyIso R i j k D P hP hD).hom =
      IntersectionPointNaturality.hilbertIntersectionTestPointEquiv R i j k D P hP hD C (hilbertPointOver (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P) f) x :=
  (hilbertIntersectionFamilyTestEquiv R i j k D P hP hD).toIso_on_affine C f x

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.IntersectionFamilyIso
