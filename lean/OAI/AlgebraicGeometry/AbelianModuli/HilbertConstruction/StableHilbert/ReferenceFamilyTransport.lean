import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.FamilyAffineComparison
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineProjectiveTransport

/-! # Reference Family Transport -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ReferenceFamilyTransport

noncomputable section

/-! The existing global stable-family transport on the original HilbertConstruction
Hilbert pullbacks. On affine overlap tests it is exactly the native
coordinate-compatible transport used by the full-level classifier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

private theorem iso_splice {C : Type*} [Category* C]
    {U V A B X Y P Q : C} (s : U ≅ A) (t : V ≅ B)
    (r : A ≅ X) (r' : B ≅ Y) (n : A ≅ P) (n' : B ≅ Q) (e : P ≅ Q) :
    (s ≪≫ r).symm ≪≫ ((s ≪≫ n) ≪≫ e ≪≫ (t ≪≫ n').symm) ≪≫ (t ≪≫ r') =
      r.symm ≪≫ n ≪≫ e ≪≫ n'.symm ≪≫ r' := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]

private theorem iso_splice_of_eq {C : Type*} [Category* C]
    {U V A B X Y P Q : C} (s : U ≅ A) (t : V ≅ B)
    (r : A ≅ X) (r' : B ≅ Y) (n : A ≅ P) (n' : B ≅ Q) (e : P ≅ Q)
    (v : U ≅ V) (h : (s ≪≫ n) ≪≫ e ≪≫ (t ≪≫ n').symm = v) :
    r.symm ≪≫ n ≪≫ e ≪≫ n'.symm ≪≫ r' = (s ≪≫ r).symm ≪≫ v ≪≫ (t ≪≫ r') :=
  (iso_splice s t r r' n n' e).symm.trans
    (congrArg (fun w => (s ≪≫ r).symm ≪≫ w ≪≫ (t ≪≫ r')) h)

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n H ≤ D)
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {T : Over (Spec (.of R))}
    (a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (b : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i k D H)
    (hab : a ≫ ChartPullbacks.stableHilbertChartToRank R i j D H = b ≫ ChartPullbacks.stableHilbertChartToRank R i k D H)

def stableHilbertOriginalFamilyTransport :
    (Over.pullback (a ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH).left).obj
        (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n H).family.scheme ≅
      (Over.pullback (b ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH).left).obj
        (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n H).family.scheme :=
  (ClassifyingMap.stableConfigurationHilbertNativePullbackRecovery R i j D H hH a).symm ≪≫
    Intrinsic.FamilyPullbackIso.nativeFamilyPullbackIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
      (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D H) ≪≫
    FamilyTransport.stableHilbertFamilyTransport R i D H hH hD j k a b hab ≪≫
    (Intrinsic.FamilyPullbackIso.nativeFamilyPullbackIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) b
      (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i k D H)).symm ≪≫
    ClassifyingMap.stableConfigurationHilbertNativePullbackRecovery R i k D H hH b

private theorem originalFamilyTransport_affine_square
    {C : Type u} [CommRing C] [IsNoetherianRing C]
    {f : Spec (.of C) ⟶ Spec (.of R)}
    (c : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (hc : (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD) ≫ ChartPullbacks.stableHilbertChartToRank R i j D H =
      (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD) ≫ ChartPullbacks.stableHilbertChartToRank R i k D H) :
    FamilyTransport.stableHilbertAffinePullbackIso R i D H (.of C) j
        (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD) ≪≫
      FamilyTransport.stableHilbertFamilyTransport R i D H hH hD j k
        (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)
        (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD) hc ≪≫
      (FamilyTransport.stableHilbertAffinePullbackIso R i D H (.of C) k
        (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD)).symm =
      IntrinsicTransport.rawHilbertNativeTransport R i j k D H hH hD c :=
  (IntersectionAffineTransportComparison.stableHilbertFamilyTransport_intersection_affine R i D H hH hD C j k c hc).trans
    (FamilyTransport.rawHilbertNativeTransport_eq_affine_of R i D H hH hD C j k c hc).symm

theorem stableHilbertOriginalFamilyTransport_affine
    {C : Type u} [CommRing C] [IsNoetherianRing C]
    {f : Spec (.of C) ⟶ Spec (.of R)}
    (c : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)
    (hc : (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD) ≫ ChartPullbacks.stableHilbertChartToRank R i j D H =
      (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD) ≫ ChartPullbacks.stableHilbertChartToRank R i k D H) :
    stableHilbertOriginalFamilyTransport R i D H hH hD j k
      (c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)
      (c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD) hc =
        AffineProjectiveEmbedding.StableHilbertAffineTransport.familyIso R i D H hH hD j k c := by
  let a := c ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD
  let b := c ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD
  let X := HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n
  let s := Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso X (AffineFamily.stableHilbertAffineFamily_pullback R (.of C) i j D H a)
  let t := Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso X (AffineFamily.stableHilbertAffineFamily_pullback R (.of C) i k D H b)
  let r := ClassifyingMap.stableConfigurationHilbertNativePullbackRecovery R i j D H hH a
  let r' := ClassifyingMap.stableConfigurationHilbertNativePullbackRecovery R i k D H hH b
  let q := Intrinsic.FamilyPullbackIso.nativeFamilyPullbackIso X a (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D H)
  let q' := Intrinsic.FamilyPullbackIso.nativeFamilyPullbackIso X b (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i k D H)
  let e := FamilyTransport.stableHilbertFamilyTransport R i D H hH hD j k a b hc
  have he : (s ≪≫ q) ≪≫ e ≪≫ (t ≪≫ q').symm = IntrinsicTransport.rawHilbertNativeTransport R i j k D H hH hD c :=
    originalFamilyTransport_affine_square R i D H hH hD j k c hc
  exact iso_splice_of_eq s t r r' q q' e _ he

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ReferenceFamilyTransport
