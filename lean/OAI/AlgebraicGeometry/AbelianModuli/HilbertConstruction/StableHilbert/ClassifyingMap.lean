import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Intrinsic.Classification
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.NoetherianCharts
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.PolynomialEquivalence

/-! # Classifying Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ClassifyingMap

noncomputable section

/-! The actual stable-chart family classified in the original HilbertConstruction Hilbert
parameter, with recovery on every test scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.PolynomialEquivalence.GradedHilbert
universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (D : ℕ) (P : Polynomial ℚ)
variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)

include hP in
theorem stableConfigurationHilbert_canonicalFiberPolynomial :
    HilbertScheme.Presentations.CanonicalFiberPolynomial.GradedHilbert.CanonicalFiberHilbertPolynomial (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P) P :=
  HilbertScheme.Presentations.Noetherian.PolynomialEquivalence.GradedHilbert.boundedHilbertUniversalFamily_canonicalFiberPolynomial
    (ι := ULift.{u} (Fin (Stable.ConfigurationLocus.configurationHilbertRank D P))) (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P hP
    (Stable.ConfigurationLocus.stableConfigurationHilbertParameterMap R i j D P)

def stableConfigurationHilbertRelativeFamily :
    RelativeProjective.Families.RelativeProjectiveHilbertFamily (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P).left n P :=
  Intrinsic.ProjectiveFamily.nativeProjectiveHilbertFamily n (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P) P
    (stableConfigurationHilbert_canonicalFiberPolynomial R i j D P hP)

def stableConfigurationHilbertClassifier :
    Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P ⟶ Hilbert.ParameterScheme.hilbertParameterScheme (Spec (.of R)) n P :=
  Intrinsic.Classification.nativeHilbertClassifier n (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P) P
    (stableConfigurationHilbert_canonicalFiberPolynomial R i j D P hP)

theorem stableConfigurationHilbertClassifier_classifies :
    (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n P).pullback (stableConfigurationHilbertClassifier R i j D P hP).left =
      stableConfigurationHilbertRelativeFamily R i j D P hP :=
  Intrinsic.Classification.nativeHilbertClassifier_classifies n (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P) P
    (stableConfigurationHilbert_canonicalFiberPolynomial R i j D P hP)

def stableConfigurationHilbertNativeRecovery :
    Intrinsic.FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n)
        (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P) (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P) ≅
      (Over.pullback (stableConfigurationHilbertClassifier R i j D P hP).left).obj
        (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n P).family.scheme :=
  Intrinsic.Classification.nativeHilbertClassifierIso n (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P) P
    (stableConfigurationHilbert_canonicalFiberPolynomial R i j D P hP)

private theorem stableConfigurationHilbertNativeRecovery_eq :
    stableConfigurationHilbertNativeRecovery R i j D P hP =
      Intrinsic.Classification.nativeProjectiveHilbertRecoveryIso n (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
        (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P) P
        (stableConfigurationHilbert_canonicalFiberPolynomial R i j D P hP)
        (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n P)
        (stableConfigurationHilbertClassifier R i j D P hP).left
        (stableConfigurationHilbertClassifier_classifies R i j D P hP) := rfl

theorem stableConfigurationHilbertNativeRecovery_ambient :
    let Q : Projective.ProjectivePresentations.ProjectivePresentation (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n P).family.scheme :=
      ⟨n, (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n P).family.inclusion, inferInstance⟩
    ((stableConfigurationHilbertNativeRecovery R i j D P hP).hom ≫
        (Q.baseChange (stableConfigurationHilbertClassifier R i j D P hP).left).embedding).left ≫
        (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P) n).hom =
      (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P).val.subschemeι := by
  rw [stableConfigurationHilbertNativeRecovery_eq]
  exact Intrinsic.Classification.nativeProjectiveHilbertRecoveryIso_ambient n (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P) P
    (stableConfigurationHilbert_canonicalFiberPolynomial R i j D P hP)
    (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n P)
    (stableConfigurationHilbertClassifier R i j D P hP).left
    (stableConfigurationHilbertClassifier_classifies R i j D P hP)

variable {T : Over (Spec (.of R))} (a : T ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)

theorem stableConfigurationHilbertClassifier_pullback_classifies :
    (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n P).pullback (a ≫ stableConfigurationHilbertClassifier R i j D P hP).left =
      Intrinsic.ProjectiveFamily.nativeProjectiveHilbertFamily n T
        (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
          (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P)) P
        ((stableConfigurationHilbert_canonicalFiberPolynomial R i j D P hP).pullback a) :=
  Intrinsic.Classification.nativeHilbertClassifier_pullback_classifies n (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P) P
    (stableConfigurationHilbert_canonicalFiberPolynomial R i j D P hP) a

def stableConfigurationHilbertNativePullbackRecovery :
    Intrinsic.FamilyTestPoints.nativeFamilyOver (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) T
        (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
          (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P)) ≅
      (Over.pullback (a ≫ stableConfigurationHilbertClassifier R i j D P hP).left).obj
        (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n P).family.scheme :=
  Intrinsic.Classification.nativeHilbertClassifierPullbackIso n (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P) P
    (stableConfigurationHilbert_canonicalFiberPolynomial R i j D P hP) a

private theorem stableConfigurationHilbertNativePullbackRecovery_eq :
    stableConfigurationHilbertNativePullbackRecovery R i j D P hP a =
      Intrinsic.Classification.nativeProjectiveHilbertRecoveryIso n T
        (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
          (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P)) P
        ((stableConfigurationHilbert_canonicalFiberPolynomial R i j D P hP).pullback a)
        (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n P)
        (a ≫ stableConfigurationHilbertClassifier R i j D P hP).left
        (stableConfigurationHilbertClassifier_pullback_classifies R i j D P hP a) := rfl

theorem stableConfigurationHilbertNativePullbackRecovery_ambient :
    let Q : Projective.ProjectivePresentations.ProjectivePresentation (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n P).family.scheme :=
      ⟨n, (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n P).family.inclusion, inferInstance⟩
    ((stableConfigurationHilbertNativePullbackRecovery R i j D P hP a).hom ≫
        (Q.baseChange (a ≫ stableConfigurationHilbertClassifier R i j D P hP).left).embedding).left ≫
        (Intrinsic.ProjectiveAmbient.nativeHilbertAmbientIso T n).hom =
      (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
        (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P)).val.subschemeι := by
  rw [stableConfigurationHilbertNativePullbackRecovery_eq]
  exact Intrinsic.Classification.nativeProjectiveHilbertRecoveryIso_ambient n T
    (HilbertScheme.Presentations.Hilbert.Functor.pullbackFamily (HilbertScheme.Presentations.Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver (Spec (.of R)) n) a
      (Stable.ConfigurationLocus.stableConfigurationHilbertUniversalFamily R i j D P)) P
    ((stableConfigurationHilbert_canonicalFiberPolynomial R i j D P hP).pullback a)
    (Hilbert.ParameterScheme.hilbertUniversalFamily (Spec (.of R)) n P)
    (a ≫ stableConfigurationHilbertClassifier R i j D P hP).left
    (stableConfigurationHilbertClassifier_pullback_classifies R i j D P hP a)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ClassifyingMap
