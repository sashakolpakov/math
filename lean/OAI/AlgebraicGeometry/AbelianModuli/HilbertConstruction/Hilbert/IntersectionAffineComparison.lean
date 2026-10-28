import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyLocalPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.IntersectionFamilyIso

/-! # Intersection Affine Comparison -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.IntersectionAffineComparison

noncomputable section

/-! The global intersection-family isomorphism pulls back to the actual
affine chart transport. The comparison tracks arbitrary local-family points. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m)
variable (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (D : ℕ) (P : Polynomial ℚ)
variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D
  (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)
variable (C : CommRingCat.{u}) [IsNoetherianRing C]
variable {f : Spec C ⟶ Spec (.of R)}
variable (a : Over.mk f ⟶
  Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)

theorem hilbertIntersectionAffineTransport_familyMap :
    HilbertScheme.Presentations.Hilbert.Functor.familyMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
        (IntersectionUniversalFamilies.hilbertIntersectionLeftFamily R i j k D P hP hD).val ≫
          (IntersectionFamilyIso.hilbertIntersectionFamilyIso R i j k D P hP hD).hom.left =
      (IntersectionUniversalFamilies.hilbertIntersectionAffineTransport R i j k D P hP hD C a).hom.left ≫
        HilbertScheme.Presentations.Hilbert.Functor.familyMap (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
          (IntersectionUniversalFamilies.hilbertIntersectionRightFamily R i j k D P hP hD).val := by
  let X : Over (Spec (.of R)) := HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n
  let T : Over (Spec (.of R)) := Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P
  let F : HilbertScheme.Presentations.Hilbert.Functor.Family X T := IntersectionUniversalFamilies.hilbertIntersectionLeftFamily R i j k D P hP hD
  let G : HilbertScheme.Presentations.Hilbert.Functor.Family X T := IntersectionUniversalFamilies.hilbertIntersectionRightFamily R i j k D P hP hD
  let FA : HilbertScheme.Presentations.Hilbert.Functor.Family X (Over.mk f) := HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a F
  let E0 : Intrinsic.FamilyTestPoints.nativeFamilyOver X T F ≅ Intrinsic.FamilyTestPoints.nativeFamilyOver X T G :=
    IntersectionFamilyIso.hilbertIntersectionFamilyIso R i j k D P hP hD
  let eA : Intrinsic.FamilyTestPoints.nativeFamilyOver X (Over.mk f) FA ≅
      Intrinsic.FamilyTestPoints.nativeFamilyOver X (Over.mk f) (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily X a G) :=
    IntersectionUniversalFamilies.hilbertIntersectionAffineTransport R i j k D P hP hD C a
  change HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val ≫ E0.hom.left =
    eA.hom.left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a G.val
  have : IsLocallyNoetherian (Over.mk f).left :=
    inferInstanceAs (IsLocallyNoetherian (Spec C))
  have hnoeth : IsLocallyNoetherian (Intrinsic.FamilyTestPoints.nativeFamilyOver X (Over.mk f) FA).left :=
    IntersectionUniversalFamilies.nativeFamilyOver_locallyNoetherian X (Over.mk f) FA
  apply @Noetherian.AffineTestMorphisms.schemeHom_ext_noetherianAffines
    (Intrinsic.FamilyTestPoints.nativeFamilyOver X (Over.mk f) FA).left (Intrinsic.FamilyTestPoints.nativeFamilyOver X T G).left hnoeth
  intro A _ x
  let r : Spec A ⟶ Spec C := x ≫ (Intrinsic.FamilyTestPoints.nativeFamilyOver X (Over.mk f) FA).hom
  let t : Spec A ⟶ T.left := r ≫ a.left
  let g : Spec A ⟶ Spec (.of R) := t ≫ T.hom
  let b : Over.mk g ⟶ Over.mk f := Over.homMk r (by
    change r ≫ f = (r ≫ a.left) ≫ T.hom
    have ha : a.left ≫ T.hom = f := a.w
    exact (congrArg (fun q => r ≫ q) ha.symm).trans (Category.assoc _ _ _).symm)
  let p : Over.mk t ⟶ Intrinsic.FamilyTestPoints.nativeFamilyOver X T F :=
    Over.homMk (x ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val) (by
      change (x ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val) ≫
          HilbertScheme.Presentations.Hilbert.Functor.familyProjection X F.val =
        (x ≫ HilbertScheme.Presentations.Hilbert.Functor.familyProjection X FA.val) ≫ a.left
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun q => x ≫ q) (HilbertScheme.Presentations.Hilbert.Functor.family_isPullback X a F.val).w.symm).trans
          (Category.assoc _ _ _).symm))
  let eB := IntersectionUniversalFamilies.hilbertIntersectionAffineTransport R i j k D P hP hD A (b ≫ a)
  let EA := Intrinsic.AffineTransportNaturality.affineNativeAmbientTransport n f
    (StableProjectiveTransport.rawStableIntersectionProjectiveIso R i j k
      (a ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D P))
  let EB := Intrinsic.AffineTransportNaturality.affineNativeAmbientTransport n g
    (StableProjectiveTransport.rawStableIntersectionProjectiveIso R i j k
      ((b ≫ a) ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D P))
  have hglobal :
      p.left ≫ E0.hom.left =
        (Intrinsic.FamilyTestPoints.nativeFamilyTestPointTransport X (b ≫ a) F G eB p).left := by
    have h := congrArg Over.Hom.left
      (IntersectionFamilyIso.hilbertIntersectionFamilyIso_on_affine R i j k D P hP hD A t p)
    exact h
  have hE : EB ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientMap X b = HilbertScheme.Presentations.Hilbert.Functor.ambientMap X b ≫ EA := by
    simpa only [EA, EB, Category.assoc] using
      AmbientTransportOverNaturality.rawStableNativeAmbientTransport_natural R i j k
        (a ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D P) g b
  have hlocal :
      (Intrinsic.FamilyTestPoints.nativeFamilyTestPointTransport X (b ≫ a) F G eB p).left =
        x ≫ eA.hom.left ≫ HilbertScheme.Presentations.Hilbert.Functor.familyMap X a G.val :=
    Intrinsic.FamilyLocalPoints.nativeFamilyTestPointTransport_from_local X a b F G eA eB EA EB
      (IntersectionUniversalFamilies.hilbertIntersectionAffineTransport_ambient R i j k D P hP hD C a)
      (IntersectionUniversalFamilies.hilbertIntersectionAffineTransport_ambient R i j k D P hP hD A (b ≫ a))
      hE x (by rfl) p rfl
  exact (Category.assoc x (HilbertScheme.Presentations.Hilbert.Functor.familyMap X a F.val) E0.hom.left).symm.trans
    (hglobal.trans hlocal)

theorem hilbertIntersectionFamilyIso_pullback_affine :
    Intrinsic.FamilyPullbackPoints.nativeFamilyIsoPullback
        (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
        (IntersectionUniversalFamilies.hilbertIntersectionLeftFamily R i j k D P hP hD)
        (IntersectionUniversalFamilies.hilbertIntersectionRightFamily R i j k D P hP hD)
        (IntersectionFamilyIso.hilbertIntersectionFamilyIso R i j k D P hP hD) =
      IntersectionUniversalFamilies.hilbertIntersectionAffineTransport R i j k D P hP hD C a := by
  apply Intrinsic.FamilyPullbackPoints.nativeFamilyIsoPullback_eq_of_familyMap
  exact hilbertIntersectionAffineTransport_familyMap R i j k D P hP hD C a

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.IntersectionAffineComparison
