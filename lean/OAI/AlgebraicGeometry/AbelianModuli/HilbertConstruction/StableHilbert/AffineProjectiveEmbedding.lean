import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntrinsicTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ClassifyingMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyPullbackComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RelativeCoordinateTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.AbelianLift

/-! # Affine Projective Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineProjectiveEmbedding

noncomputable section

/-! The actual overlap isomorphism of stable Hilbert families, expressed
on the original HilbertConstruction Hilbert pullbacks and their original projective
presentations. Its coordinate square gives the O(1) isomorphism needed
by the bounded full-level classifier. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private theorem recovered_embedding_transport {C : Type*} [Category* C]
    {F G X Y P Q : C} (rF : F ≅ X) (rG : G ≅ Y) (e : F ≅ G)
    (i : X ⟶ P) (j : Y ⟶ P) (q : P ⟶ Q) [Mono q]
    (a : P ⟶ P) (c : Q ⟶ Q) (f : F ⟶ Q) (g : G ⟶ Q)
    (hF : rF.hom ≫ i ≫ q = f) (hG : rG.hom ≫ j ≫ q = g)
    (he : e.hom ≫ g = f ≫ c) (ha : a ≫ q = q ≫ c) :
    (rF.symm ≪≫ e ≪≫ rG).hom ≫ j = i ≫ a := by
  apply (cancel_epi rF.hom).mp
  apply (cancel_mono q).mp
  have hR : (rF.hom ≫ (i ≫ a)) ≫ q = f ≫ c := by
    calc
      _ = rF.hom ≫ i ≫ (a ≫ q) := by simp only [Category.assoc]
      _ = rF.hom ≫ i ≫ (q ≫ c) := congrArg (fun z => rF.hom ≫ i ≫ z) ha
      _ = (rF.hom ≫ i ≫ q) ≫ c := by simp only [Category.assoc]
      _ = f ≫ c := congrArg (fun z => z ≫ c) hF
  calc
    _ = e.hom ≫ g := by
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, rF.hom_inv_id_assoc, hG]
    _ = f ≫ c := he
    _ = (rF.hom ≫ (i ≫ a)) ≫ q := hR.symm

private theorem baseChange_embedding_left
    {B U : Scheme.{u}} {X : Over B} (P : Projective.ProjectivePresentations.ProjectivePresentation X) (f : U ⟶ B) :
    (P.baseChange f).embedding.left =
      ((Over.pullback f).map P.embedding).left ≫
        (Projective.SpaceBaseChange.projectiveSpaceOverBaseChangeIso f P.dimension).inv.left := rfl

private def nativePullbackEmbedding
    {S : Scheme.{u}} (n : ℕ) (H : Polynomial ℚ) {T : Over S}
    (b : T ⟶ Hilbert.ParameterScheme.hilbertParameterScheme S n H) :
    ((Over.pullback b.left).obj (Hilbert.ParameterScheme.hilbertUniversalFamily S n H).family.scheme).left ⟶
      (Projective.ProjectivePresentations.projectiveSpaceOver T.left n).left :=
  ((Over.pullback b.left).map (Hilbert.ParameterScheme.hilbertUniversalFamily S n H).family.inclusion).left ≫
    (Projective.SpaceBaseChange.projectiveSpaceOverBaseChangeIso b.left n).inv.left

private theorem stableRecovery_eq
    (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    {T : Over (Spec (.of R))} (a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H) :
    ClassifyingMap.stableConfigurationHilbertNativePullbackRecovery R i j D H hH a =
      Intrinsic.Classification.nativeProjectiveHilbertRecoveryIso n T
        (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
          (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D H)) H
        ((ClassifyingMap.stableConfigurationHilbert_canonicalFiberPolynomial R i j D H hH).pullback a)
        (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n H)
        (a ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH).left
        (ClassifyingMap.stableConfigurationHilbertClassifier_pullback_classifies R i j D H hH a) := rfl

private theorem stableRecovery_ambient
    (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    {T : Over (Spec (.of R))} (a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H) :
    (ClassifyingMap.stableConfigurationHilbertNativePullbackRecovery R i j D H hH a).hom.left ≫
      nativePullbackEmbedding n H (a ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH) ≫
        (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso T n).hom =
      (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
        (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D H)).val.subschemeι := by
  rw [stableRecovery_eq]
  exact Intrinsic.Classification.nativeProjectiveHilbertRecoveryIso_ambient_left n T
    (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
      (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D H)) H
    ((ClassifyingMap.stableConfigurationHilbert_canonicalFiberPolynomial R i j D H hH).pullback a)
    (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n H)
    (a ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH).left
    (ClassifyingMap.stableConfigurationHilbertClassifier_pullback_classifies R i j D H hH a)

private theorem identityAffineChart_nativeAmbient
    {S : Scheme.{u}} {C : Type u} [CommRing C] (f : Spec (.of C) ⟶ S) (n : ℕ) :
    AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n ≫
      (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso (Over.mk f) n).hom = (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).hom := by
  let T : Over S := Over.mk f
  apply (Over.isPullback_of_binaryFan_isLimit _ (prodIsProd T (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n))).hom_ext
  · change (AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n ≫
        (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso T n).hom) ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T =
      (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).hom ≫ HilbertScheme.Presentations.Hilbert.Functor.ambientProjection (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) T
    rw [Category.assoc, Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso_projection, AffineProjective.Charts.affineProjectiveChartMap_over,
      Category.comp_id, Intrinsic.ProjectiveAmbient.affineProjectiveSpace_hom_eq_native, HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso_projection]
  · let q := (prod.snd : T ⨯ HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n ⟶ HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left
    let m := HilbertScheme.Presentations.Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap f n
    have hL : (AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n ≫
        (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso T n).hom) ≫ q = HilbertScheme.Presentations.Projective.Point.GradedHilbert.projectiveSchemePointMap n f := by
      have hc := congrArg (fun z : (Projective.ProjectivePresentations.affineProjectiveSpace C n).left ⟶
          (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of C)) n).left => z ≫ m)
        (Intrinsic.ProjectiveAmbient.nativeProjectiveSpaceIso_affine (Spec (.of C)) n (𝟙 (Spec (.of C))))
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun z => AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n ≫ z)
          (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso_projective T n)).trans
          ((Category.assoc _ _ _).symm.trans (hc.trans
            ((HilbertScheme.Presentations.Projective.PointComposition.GradedHilbert.projectiveSchemePointMap_comp n (𝟙 (Spec (.of C))) f).trans
              (congrArg (HilbertScheme.Presentations.Projective.Point.GradedHilbert.projectiveSchemePointMap n) (Category.id_comp f))))))
    exact hL.trans (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso_projective n f).symm

private theorem affineConfigurationRelativeIso_nativeAmbient
    {S : Scheme.{u}} {C : Type u} [CommRing C] {n : ℕ} (f : Spec (.of C) ⟶ S)
    {ι : Type*} (v w : ι → Fin (n + 1) → C) (h : Configuration.ProjectiveTransport.ConfigurationFrameRelated v w) :
    (Affine.RelativeCoordinateTransport.affineConfigurationRelativeIso v w h).hom.left ≫ (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso (Over.mk f) n).hom =
      (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso (Over.mk f) n).hom ≫
        Intrinsic.AffineTransportNaturality.affineNativeAmbientTransport n f (Configuration.ProjectiveTransport.configurationProjectiveTransport v w h) := by
  let q : Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading C n) ⟶ (Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of C)) n).left :=
    (RelativeProjective.TwistingSectionsFinite.identityAffineProjectiveChartIso (R := C) (n := n)).hom.left
  let p := (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso (Over.mk f) n).hom
  let a := (Affine.RelativeCoordinateTransport.affineConfigurationRelativeIso v w h).hom.left
  let E : Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading C n) ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading C n) := (Configuration.ProjectiveTransport.configurationProjectiveTransport v w h).hom.left
  let d := HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f
  have hq : q ≫ p = d.hom := identityAffineChart_nativeAmbient f n
  have ha : E ≫ q = q ≫ a := congrArg Over.Hom.left (Affine.RelativeCoordinateTransport.affineConfigurationRelativeIso_chart v w h)
  let : IsIso q := (Over.forget _).map_isIso (RelativeProjective.TwistingSectionsFinite.identityAffineProjectiveChartIso (R := C) (n := n)).hom
  apply (cancel_epi q).mp
  change q ≫ (a ≫ p) = q ≫ (p ≫ (d.inv ≫ E ≫ d.hom))
  calc
    _ = (E ≫ q) ≫ p := (Category.assoc _ _ _).symm.trans (congrArg (fun z => z ≫ p) ha.symm)
    _ = E ≫ d.hom := (Category.assoc _ _ _).trans (congrArg (fun z => E ≫ z) hq)
    _ = q ≫ (p ≫ (d.inv ≫ E ≫ d.hom)) := by
      rw [← Category.assoc q p, hq, d.hom_inv_id_assoc]

private def composeTwoRecoveryIsos {S : Scheme.{u}} {X Y Z : Over S}
    (a : X ≅ Y) (b : Y ≅ Z) : X ≅ Z := a ≪≫ b

private theorem composeTwoRecoveryIsos_ambient
    {S : Scheme.{u}} {X Y Z : Over S} {P Q : Scheme.{u}}
    (a : X ≅ Y) (b : Y ≅ Z) (i : Z.left ⟶ P) (q : P ⟶ Q)
    (j : Y.left ⟶ Q) (k : X.left ⟶ Q)
    (hb : b.hom.left ≫ i ≫ q = j) (ha : a.hom.left ≫ j = k) :
    (composeTwoRecoveryIsos a b).hom.left ≫ i ≫ q = k := by
  change (a.hom.left ≫ b.hom.left) ≫ i ≫ q = k
  simp only [Category.assoc, hb, ha]

private theorem embedding_eq_of_replacements {C : Type*} [Category* C]
    {X Y P : C} (e : X ⟶ Y) (a : P ⟶ P)
    {i i' : Y ⟶ P} {j j' : X ⟶ P}
    (hi : i = i') (hj : j = j') (h : e ≫ i' = j' ≫ a) : e ≫ i = j ≫ a :=
  (congrArg (fun q => e ≫ q) hi).trans
    (h.trans (congrArg (fun q => q ≫ a) hj.symm))

namespace StableHilbertAffineTransport

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Type u} [CommRing C] [IsNoetherianRing C]
    {n m : ℕ} (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n H ≤ D)
    (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    {f : Spec (.of C) ⟶ Spec (.of R)}

private def chartRecovery (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (b : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H) :
    Intrinsic.AffineFamilyTransport.affineNativeFamilyOver n f (AffineFamily.stableHilbertAffineFamily R (.of C) i j D H b) ≅
      (Over.pullback (b ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH).left).obj
        (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n H).family.scheme :=
  composeTwoRecoveryIsos
    (Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
      (AffineFamily.stableHilbertAffineFamily_pullback R (.of C) i j D H b))
    (ClassifyingMap.stableConfigurationHilbertNativePullbackRecovery R i j D H hH b)

omit [IsNoetherianRing C] in
private theorem chartRecovery_ambient (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (b : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H) :
    (chartRecovery R i D H hH j b).hom.left ≫
      nativePullbackEmbedding n H (b ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH) ≫
      (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso (Over.mk f) n).hom =
        (AffineFamily.stableHilbertAffineFamily R (.of C) i j D H b).val.subschemeι := by
  let q := Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
    (AffineFamily.stableHilbertAffineFamily_pullback R (.of C) i j D H b)
  let r := ClassifyingMap.stableConfigurationHilbertNativePullbackRecovery R i j D H hH b
  exact composeTwoRecoveryIsos_ambient q r
    (nativePullbackEmbedding n H (b ≫ ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH))
    (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso (Over.mk f) n).hom _ _
    (stableRecovery_ambient R i j D H hH b)
    (Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso_hom_ambient _ (AffineFamily.stableHilbertAffineFamily_pullback R (.of C) i j D H b))

variable (b : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i (j.intersection k) D H)

def leftPoint : Over.mk f ⟶ Hilbert.ParameterScheme.hilbertParameterScheme (Spec (.of R)) n H :=
  (b ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD) ≫
    ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH

def rightPoint : Over.mk f ⟶ Hilbert.ParameterScheme.hilbertParameterScheme (Spec (.of R)) n H :=
  (b ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD) ≫
    ClassifyingMap.stableConfigurationHilbertClassifier R i k D H hH

def familyIso :
    (Over.pullback (leftPoint R i D H hH hD j k b).left).obj
        (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n H).family.scheme ≅
      (Over.pullback (rightPoint R i D H hH hD j k b).left).obj
        (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n H).family.scheme :=
  (chartRecovery R i D H hH j (b ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)).symm ≪≫
    IntrinsicTransport.rawHilbertNativeTransport R i j k D H hH hD b ≪≫
      chartRecovery R i D H hH k (b ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD)

def coordinateIso : Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of C)) n ≅ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of C)) n :=
  let x := b ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D H
  Affine.RelativeCoordinateTransport.affineConfigurationRelativeIso
    (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i j (.of C) (x ≫ StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k))
    (Stable.PolynomialMatrixCoefficients.stablePolynomialChartPointVectors R i k (.of C) (x ≫ StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k))
    (StableChartFrames.stablePolynomialIntersection_frameRelated R i j k x)

theorem familyIso_native_embedding :
    (familyIso R i D H hH hD j k b).hom.left ≫
      nativePullbackEmbedding n H (rightPoint R i D H hH hD j k b) =
      nativePullbackEmbedding n H (leftPoint R i D H hH hD j k b) ≫
        (coordinateIso R i D H j k b).hom.left := by
  let rF := chartRecovery R i D H hH j (b ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD)
  let rG := chartRecovery R i D H hH k (b ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD)
  let e := IntrinsicTransport.rawHilbertNativeTransport R i j k D H hH hD b
  let x := b ≫ IntrinsicTransport.stableHilbertChartAmbientMap R i (j.intersection k) D H
  let p := (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso (Over.mk f) n).hom
  exact recovered_embedding_transport ((Over.forget _).mapIso rF) ((Over.forget _).mapIso rG)
    ((Over.forget _).mapIso e) _ _ p (coordinateIso R i D H j k b).hom.left
    (Intrinsic.AffineTransportNaturality.affineNativeAmbientTransport n f (StableProjectiveTransport.rawStableIntersectionProjectiveIso R i j k x)) _ _
    (chartRecovery_ambient R i D H hH j (b ≫ IntersectionMaps.stableHilbertIntersectionLeftMap R i j k D H hH hD))
    (chartRecovery_ambient R i D H hH k (b ≫ IntersectionMaps.stableHilbertIntersectionRightMap R i j k D H hH hD))
    (IntrinsicTransport.rawHilbertNativeTransport_ambient R i j k D H hH hD b)
    (affineConfigurationRelativeIso_nativeAmbient f _ _ (StableChartFrames.stablePolynomialIntersection_frameRelated R i j k x))

theorem familyIso_embedding_left :
    (familyIso R i D H hH hD j k b).hom.left ≫
      ((Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) n H).baseChange
        (rightPoint R i D H hH hD j k b).left).embedding.left =
      ((Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) n H).baseChange
        (leftPoint R i D H hH hD j k b).left).embedding.left ≫
        (coordinateIso R i D H j k b).hom.left := by
  exact embedding_eq_of_replacements
    (familyIso R i D H hH hD j k b).hom.left (coordinateIso R i D H j k b).hom.left
    (baseChange_embedding_left (Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) n H)
      (rightPoint R i D H hH hD j k b).left)
    (baseChange_embedding_left (Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) n H)
      (leftPoint R i D H hH hD j k b).left)
    (familyIso_native_embedding R i D H hH hD j k b)

theorem familyIso_embedding :
    (familyIso R i D H hH hD j k b).hom ≫
      ((Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) n H).baseChange
        (rightPoint R i D H hH hD j k b).left).embedding =
      ((Intrinsic.Presentation.NativeHilbertAbelianLift.presentation (Spec (.of R)) n H).baseChange
        (leftPoint R i D H hH hD j k b).left).embedding ≫
        (coordinateIso R i D H j k b).hom := by
  apply Over.OverMorphism.ext
  exact familyIso_embedding_left R i D H hH hD j k b

end StableHilbertAffineTransport

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.AffineProjectiveEmbedding
