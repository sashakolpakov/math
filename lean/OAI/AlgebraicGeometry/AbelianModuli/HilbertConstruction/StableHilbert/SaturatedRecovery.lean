import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedIntrinsicFamilyRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ClassifyingMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.Presentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.FamilyPullbackComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.RelativeCoordinateTransport

/-! # Saturated Recovery -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SaturatedRecovery.StableHilbertSaturatedRecovery

noncomputable section

/-! Equality of a stable-chart Hilbert family with the original saturated
family gives an isomorphism to the original universal Hilbert fiber.
Its projective embedding is the original homogeneous embedding. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

private def composeRecoveredIsos {S : Scheme.{u}} {X₀ X₁ X₂ X₃ : Over S}
    (e₀ : X₀ ≅ X₁) (e₁ : X₁ ≅ X₂) (e₂ : X₂ ≅ X₃) : X₀ ≅ X₃ :=
  e₀ ≪≫ e₁ ≪≫ e₂

private theorem composeRecoveredIsos_ambient
    {S : Scheme.{u}} {X₀ X₁ X₂ X₃ : Over S} {Y Z : Scheme.{u}}
    (e₀ : X₀ ≅ X₁) (e₁ : X₁ ≅ X₂) (e₂ : X₂ ≅ X₃)
    (j : X₃.left ⟶ Y) (a : Y ⟶ Z) (k : X₂.left ⟶ Z) (l : X₁.left ⟶ Z)
    (h₂ : e₂.hom.left ≫ j ≫ a = k) (h₁ : e₁.hom.left ≫ k = l) :
    (composeRecoveredIsos e₀ e₁ e₂).hom.left ≫ j ≫ a = e₀.hom.left ≫ l := by
  change (e₀.hom.left ≫ e₁.hom.left ≫ e₂.hom.left) ≫ j ≫ a = _
  simp only [Category.assoc, h₂, h₁]

private def pullbackCompositeIso {X Y Z : Scheme.{u}}
    (a : X ⟶ Y) (i : Y ⟶ Z) (p : X ⟶ Z) (h : a ≫ i = p) (L : Z.Modules) :
    (Scheme.Modules.pullback a).obj ((Scheme.Modules.pullback i).obj L) ≅
      (Scheme.Modules.pullback p).obj L :=
  (Scheme.Modules.pullbackComp a i).app L ≪≫ (Scheme.Modules.pullbackCongr h).app L

private abbrev nativePresentation (S : Scheme.{u}) (n : ℕ) (H : Polynomial ℚ) :
    Projective.ProjectivePresentations.ProjectivePresentation (Hilbert.ParameterScheme.hilbertUniversalFamily S n H).family.scheme :=
  ⟨n, (Hilbert.ParameterScheme.hilbertUniversalFamily S n H).family.inclusion, inferInstance⟩

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

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
    {C : Type u} [CommRing C] [IsNoetherianRing C] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    {f : Spec (.of C) ⟶ Spec (.of R)}
    (a : Over.mk f ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (I : SaturatedFlatIdeals.SaturatedFlatHilbertIdeal C n H)
    (hI : HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
      (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D H) = I.nativeHilbertFamily f)

local notation "b" => a ≫ OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ClassifyingMap.stableConfigurationHilbertClassifier R i j D H hH
local notation "P" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SaturatedRecovery.StableHilbertSaturatedRecovery.nativePresentation (Spec (CommRingCat.of R)) n H
local notation "J" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SaturatedRecovery.StableHilbertSaturatedRecovery.nativePullbackEmbedding n H b

def iso : Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal ≅
    (Over.pullback (b).left).obj (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n H).family.scheme :=
  composeRecoveredIsos (I.nativeFamilyIso f)
    (Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) hI.symm)
    (ClassifyingMap.stableConfigurationHilbertNativePullbackRecovery R i j D H hH a)

private theorem iso_hom_left : (iso R i j D H hH a I hI).hom.left =
    (composeRecoveredIsos (I.nativeFamilyIso f)
      (Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) hI.symm)
      (ClassifyingMap.stableConfigurationHilbertNativePullbackRecovery R i j D H hH a)).hom.left := rfl

omit [IsNoetherianRing C] in
private theorem lastRecovery_nativeAmbient :
    (ClassifyingMap.stableConfigurationHilbertNativePullbackRecovery R i j D H hH a).hom.left ≫
      J ≫ (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso (Over.mk f) n).hom =
      (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
        (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D H)).val.subschemeι :=
  stableRecovery_ambient R i j D H hH (T := Over.mk f) a

private theorem composition_nativeAmbient :
    (composeRecoveredIsos (I.nativeFamilyIso f)
      (Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) hI.symm)
      (ClassifyingMap.stableConfigurationHilbertNativePullbackRecovery R i j D H hH a)).hom.left ≫
        J ≫ (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso (Over.mk f) n).hom =
      (I.nativeFamilyIso f).hom.left ≫ (I.nativeHilbertFamily f).val.subschemeι :=
  composeRecoveredIsos_ambient (I.nativeFamilyIso f)
    (Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) hI.symm)
    (ClassifyingMap.stableConfigurationHilbertNativePullbackRecovery R i j D H hH a)
    J (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso (Over.mk f) n).hom
    (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
      (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D H)).val.subschemeι
    (I.nativeHilbertFamily f).val.subschemeι
    (lastRecovery_nativeAmbient R i j D H hH a)
    (Intrinsic.FamilyPullbackComposition.nativeFamilyEqIso_hom_ambient (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) hI.symm)

theorem iso_nativeAmbient :
    (iso R i j D H hH a I hI).hom.left ≫ ((P).baseChange (b).left).embedding.left ≫
      (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso (Over.mk f) n).hom =
        HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal ≫ (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).hom := by
  rw [baseChange_embedding_left]
  exact (congrArg (fun q : (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal).left ⟶
      ((Over.pullback (b).left).obj (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n H).family.scheme).left =>
      q ≫ J ≫ (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso (Over.mk f) n).hom)
      (iso_hom_left R i j D H hH a I hI)).trans
    ((composition_nativeAmbient R i j D H hH a I hI).trans (I.nativeFamilyIso_ambient f))

private theorem iso_embedding_left :
    (iso R i j D H hH a I hI).hom.left ≫ ((P).baseChange (b).left).embedding.left =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal ≫ AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n := by
  apply (cancel_mono (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso (Over.mk f) n).hom).mp
  have hc : AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n ≫
      (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso (Over.mk f) n).hom = (HilbertScheme.Presentations.Affine.ProjectiveAmbient.GradedHilbert.affineProjectiveAmbientIso n f).hom :=
    identityAffineChart_nativeAmbient f n
  change ((iso R i j D H hH a I hI).hom.left ≫ ((P).baseChange (b).left).embedding.left) ≫ _ =
    (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal ≫ AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n) ≫ _
  exact (Category.assoc _ _ _).trans ((iso_nativeAmbient R i j D H hH a I hI).trans
    ((congrArg (fun p => HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal ≫ p) hc).symm.trans
      (Category.assoc _ _ _).symm))

theorem iso_embedding :
    (iso R i j D H hH a I hI).hom ≫ ((P).baseChange (b).left).embedding =
      Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding I.ideal ≫
        (RelativeProjective.TwistingSectionsFinite.identityAffineProjectiveChartIso (R := C) (n := n)).hom := by
  apply Over.OverMorphism.ext
  exact iso_embedding_left R i j D H hH a I hI

def sourceIso {X : Over (Spec (.of C))} (e : X ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal) :
    X ≅ (Over.pullback (b).left).obj (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n H).family.scheme :=
  e ≪≫ iso R i j D H hH a I hI

private theorem sourceIso_hom_left {X : Over (Spec (.of C))}
    (e : X ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal) :
    (sourceIso R i j D H hH a I hI e).hom.left =
      e.hom.left ≫ (iso R i j D H hH a I hI).hom.left := rfl

theorem sourceIso_embedding_left {X : Over (Spec (.of C))}
    (e : X ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal)
    (p : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of C)) n)
    (hp : (e.hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal) ≫
      AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n = p.left) :
    (sourceIso R i j D H hH a I hI e).hom.left ≫ ((P).baseChange (b).left).embedding.left = p.left := by
  have hr := iso_embedding_left R i j D H hH a I hI
  exact (congrArg (fun q : X.left ⟶
      ((Over.pullback (b).left).obj (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n H).family.scheme).left =>
      q ≫ ((P).baseChange (b).left).embedding.left)
      (sourceIso_hom_left R i j D H hH a I hI e)).trans
    ((Category.assoc _ _ _).trans ((congrArg (fun f => e.hom.left ≫ f) hr).trans
      ((Category.assoc _ _ _).symm.trans hp)))

theorem sourceIso_embedding {X : Over (Spec (.of C))}
    (e : X ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal)
    (p : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of C)) n)
    (hp : (e.hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal) ≫
      AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n = p.left) :
    (sourceIso R i j D H hH a I hI e).hom ≫ ((P).baseChange (b).left).embedding = p := by
  apply Over.OverMorphism.ext
  exact sourceIso_embedding_left R i j D H hH a I hI e p hp

def sourceTwistingIso {X : Over (Spec (.of C))}
    (e : X ≅ Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I.ideal)
    (p : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (.of C)) n)
    (hp : (e.hom.left ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I.ideal) ≫
      AffineProjective.Charts.affineProjectiveChartMap (𝟙 (Spec (.of C))) n = p.left) :
    (((P).baseChange (b).left).ampleLineBundle.pullback
      (sourceIso R i j D H hH a I hI e).hom.left).sheaf ≅
        ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of C)) n).pullback p.left).sheaf := by
  let r := (sourceIso R i j D H hH a I hI e).hom.left
  let emb := ((P).baseChange (b).left).embedding.left
  have hj : r ≫ emb = p.left :=
    sourceIso_embedding_left R i j D H hH a I hI e p hp
  exact pullbackCompositeIso r emb p.left hj (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of C)) n).sheaf

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.SaturatedRecovery.StableHilbertSaturatedRecovery
