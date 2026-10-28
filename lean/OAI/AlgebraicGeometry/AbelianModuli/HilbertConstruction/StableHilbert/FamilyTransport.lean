import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FamilyPullbacks
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ChartTransport

/-! # Family Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FamilyTransport

noncomputable section

/-! Universal chart families have canonical transports over every
test scheme with compatible stable Hilbert coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u v

private def pullbackAlongFactorIso
    {S T U : Scheme.{u}} (a : U ⟶ T) (b : T ⟶ S) (c : U ⟶ S)
    (h : a ≫ b = c) (X : Over S) :
    (Over.pullback a).obj ((Over.pullback b).obj X) ≅ (Over.pullback c).obj X :=
  (Over.pullbackComp a b).symm.app X ≪≫
    eqToIso (congrArg (fun f : U ⟶ S => (Over.pullback f).obj X) h)

/-- Pull back an overlap family isomorphism along the canonical intersection lift. -/
def chartFamilyPullbackTransport
    {S : Scheme.{u}} {W A B Z : Over S}
    {l : W ⟶ A} {r : W ⟶ B} {p : A ⟶ Z} {q : B ⟶ Z}
    (H : IsPullback l r p q) (F : Over A.left) (G : Over B.left)
    (e : (Over.pullback l.left).obj F ≅ (Over.pullback r.left).obj G)
    {T : Over S} (a : T ⟶ A) (b : T ⟶ B) (h : a ≫ p = b ≫ q) :
    (Over.pullback a.left).obj F ≅ (Over.pullback b.left).obj G := by
  let c := H.lift a b h
  let eL := pullbackAlongFactorIso c.left l.left a.left
    (congrArg Over.Hom.left (H.lift_fst a b h)) F
  let eR := pullbackAlongFactorIso c.left r.left b.left
    (congrArg Over.Hom.left (H.lift_snd a b h)) G
  exact eL.symm ≪≫ (Over.pullback c.left).mapIso e ≪≫ eR

private theorem projectiveTransport_congr
    {R : Type u} [CommRing R] {n : ℕ} {ι : Type v}
    {v₁ v₂ w₁ w₂ : ι → Fin (n + 1) → R}
    (hv : v₁ = v₂) (hw : w₁ = w₂)
    (h₁ : Configuration.ProjectiveTransport.ConfigurationFrameRelated v₁ w₁)
    (h₂ : Configuration.ProjectiveTransport.ConfigurationFrameRelated v₂ w₂) :
    Configuration.ProjectiveTransport.configurationProjectiveTransport v₁ w₁ h₁ =
      Configuration.ProjectiveTransport.configurationProjectiveTransport v₂ w₂ h₂ := by
  subst v₂
  subst w₂
  rfl

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m) (D : ℕ) (P : Polynomial ℚ)
variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)

section Transport

variable (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable {T : Over (Spec (.of R))}
variable (a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
variable (b : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D P)
variable (h : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D P =
  b ≫ ChartPullbacks.stableHilbertChartToRank R i k D P)

def stableHilbertFamilyTransport :
    (Over.pullback a.left).obj (FamilyPullbacks.stableHilbertChartFamily R i D P j) ≅
      (Over.pullback b.left).obj (FamilyPullbacks.stableHilbertChartFamily R i D P k) :=
  chartFamilyPullbackTransport (ChartPullbacks.stableHilbertChartIntersection_isPullback R i j k D P hP hD)
    (FamilyPullbacks.stableHilbertChartFamily R i D P j) (FamilyPullbacks.stableHilbertChartFamily R i D P k)
    (FamilyPullbacks.stableHilbertOverlapFamilyIso R i D P hP hD j k) a b h

@[reassoc]
theorem stableHilbertFamilyTransport_hom_base :
    (stableHilbertFamilyTransport R i D P hP hD j k a b h).hom.left ≫
        pullback.snd (FamilyPullbacks.stableHilbertChartFamily R i D P k).hom b.left =
      pullback.snd (FamilyPullbacks.stableHilbertChartFamily R i D P j).hom a.left :=
  (stableHilbertFamilyTransport R i D P hP hD j k a b h).hom.w

@[reassoc]
theorem stableHilbertFamilyTransport_inv_base :
    (stableHilbertFamilyTransport R i D P hP hD j k a b h).inv.left ≫
        pullback.snd (FamilyPullbacks.stableHilbertChartFamily R i D P j).hom a.left =
      pullback.snd (FamilyPullbacks.stableHilbertChartFamily R i D P k).hom b.left :=
  (stableHilbertFamilyTransport R i D P hP hD j k a b h).inv.w

end Transport

def stableHilbertAffinePullbackIso
    (C : CommRingCat.{u}) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {f : Spec C ⟶ Spec (.of R)}
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P) :
    Intrinsic.AffineFamilyTransport.affineNativeFamilyOver n f (AffineFamily.stableHilbertAffineFamily R C i j D P a) ≅
      (Over.pullback a.left).obj (FamilyPullbacks.stableHilbertChartFamily R i D P j) :=
  eqToIso (congrArg
    (fun F : HilbertScheme.Presentations.Hilbert.Functor.Family (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) (Over.mk f) =>
      Intrinsic.FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) (Over.mk f) F)
    (AffineFamily.stableHilbertAffineFamily_pullback R C i j D P a)) ≪≫
  Intrinsic.FamilyPullbackIso.nativeFamilyPullbackIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
    (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P)

private theorem rawAffineProjectiveTransport_eq
    (C : Type u) [CommRing C]
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) {f : Spec (.of C) ⟶ Spec (.of R)}
    (c : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)
    (h : (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD) ≫
        ChartPullbacks.stableHilbertChartToRank R i j D P =
      (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD) ≫
        ChartPullbacks.stableHilbertChartToRank R i k D P) :
 Configuration.ProjectiveTransport.configurationProjectiveTransport
      (CompatibleChartFrames.affineHilbertChartVectors R i j D P (.of C)
        (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD))
      (CompatibleChartFrames.affineHilbertChartVectors R i k D P (.of C)
        (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD))
      (CompatibleChartFrames.affineHilbertChartVectors_related R i j k D P (.of C) hP hD
        (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)
        (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD) h) =
      StableProjectiveTransport.rawStableIntersectionProjectiveIso R i j k
        (c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D P) := by
  have hj : (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD) ≫
      IntrinsicTransport.stableHilbertChartAmbientMap R i j D P =
      (c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D P) ≫
        StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k := by
    rw [Category.assoc, IntrinsicTransport.stableHilbertIntersectionLeftMap_toAmbient, ← Category.assoc]
  have hk : (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD) ≫
      IntrinsicTransport.stableHilbertChartAmbientMap R i k D P =
      (c ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D P) ≫
        StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k := by
    rw [Category.assoc, IntrinsicTransport.stableHilbertIntersectionRightMap_toAmbient, ← Category.assoc]
  exact projectiveTransport_congr
    (congrArg (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of C)) hj)
    (congrArg (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i k (.of C)) hk) _ _

theorem rawHilbertNativeTransport_eq_affine_of
    (C : Type u) [CommRing C] [IsNoetherianRing C]
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) {f : Spec (.of C) ⟶ Spec (.of R)}
    (c : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)
    (h : (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD) ≫
        ChartPullbacks.stableHilbertChartToRank R i j D P =
      (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD) ≫
        ChartPullbacks.stableHilbertChartToRank R i k D P) :
    IntrinsicTransport.rawHilbertNativeTransport R (C := C) i j k D P hP hD (f := f) c =
      Affine.ChartTransport.affineHilbertChartFamilyTransport R i j k D P hP hD (.of C)
        (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)
        (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD) h := by
  have hE := rawAffineProjectiveTransport_eq R i D P hP hD C j k c h
  have he := Affine.ChartTransport.affineHilbertChartFamilyTransport_ambient R i j k D P hP hD (.of C)
    (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)
    (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD) h
  rw [hE] at he
  exact ((IntrinsicTransport.rawHilbertNativeTransport_existsUnique R i j k D P hP hD c).choose_spec.2
    (Affine.ChartTransport.affineHilbertChartFamilyTransport R i j k D P hP hD (.of C)
      (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)
      (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD) h) he).symm

theorem rawHilbertNativeTransport_eq_affine
    (C : CommRingCat.{u}) [IsNoetherianRing C]
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) {f : Spec (.of C) ⟶ Spec (.of R)}
    (c : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D P)
    (h : (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD) ≫
        ChartPullbacks.stableHilbertChartToRank R i j D P =
      (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD) ≫
        ChartPullbacks.stableHilbertChartToRank R i k D P) :
    IntrinsicTransport.rawHilbertNativeTransport R (C := C) i j k D P hP hD (f := f) c =
      Affine.ChartTransport.affineHilbertChartFamilyTransport R i j k D P hP hD (.of C)
        (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D P hP hD)
        (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D P hP hD) h :=
  rawHilbertNativeTransport_eq_affine_of R i D P hP hD C j k c h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FamilyTransport
