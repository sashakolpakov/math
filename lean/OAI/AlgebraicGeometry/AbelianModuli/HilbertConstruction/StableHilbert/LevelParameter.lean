import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ClassifyingMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ChartQuasiProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.HilbertLevel.LevelPullbackGeometry
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PrescribedLevelAmbientParameter

/-! # Level Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelParameter.StableHilbertLevel

noncomputable section

/-! Pull the bounded group and full-level parameter to each actual
stable Hilbert chart, then require every ordered torsion label to equal
its specified configuration point in the original projective space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (D : ℕ) (P : Polynomial ℚ)
    (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
    (g : ℕ) (Pm Pi : Polynomial ℚ) (N : ℕ) [NeZero N]

def base : Over (Spec (.of R)) :=
  HilbertLevel.PullbackParameter.HilbertLevelPullback.parameter (Spec (.of R)) n P g Pm Pi N
    (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (ClassifyingMap.stableConfigurationHilbertClassifier R i j D P hP)

def toChart : base R i j D P hP g Pm Pi N ⟶ Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P :=
  HilbertLevel.PullbackParameter.HilbertLevelPullback.toChart (Spec (.of R)) n P g Pm Pi N
    (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (ClassifyingMap.stableConfigurationHilbertClassifier R i j D P hP)

def baseFamily : Level.Data.AbelianSchemeWithFullLevel g N (base R i j D P hP g Pm Pi N).left :=
  HilbertLevel.PullbackParameter.HilbertLevelPullback.family (Spec (.of R)) n P g Pm Pi N
    (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (ClassifyingMap.stableConfigurationHilbertClassifier R i j D P hP)

def basePresentation : Projective.ProjectivePresentations.ProjectivePresentation (baseFamily R i j D P hP g Pm Pi N).abelian.scheme :=
  HilbertLevel.PullbackParameter.HilbertLevelPullback.projective (Spec (.of R)) n P g Pm Pi N
    (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (ClassifyingMap.stableConfigurationHilbertClassifier R i j D P hP)

def baseQuasiProjective : Projective.ProjectivePresentations.QuasiProjectivePresentation (base R i j D P hP g Pm Pi N) :=
  HilbertLevel.LevelPullbackGeometry.HilbertLevelPullback.quasiProjective (Spec (.of R)) n P g Pm Pi N
    (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P)
    (ClassifyingMap.stableConfigurationHilbertClassifier R i j D P hP)
    (ChartQuasiProjectivity.stableConfigurationHilbertChartQuasiProjective R i j D P)

instance base_noetherian : IsNoetherian (base R i j D P hP g Pm Pi N).left :=
  (baseQuasiProjective R i j D P hP g Pm Pi N).noetherian

def toCoefficientChart : base R i j D P hP g Pm Pi N ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j :=
  toChart R i j D P hP g Pm Pi N ≫ Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P ≫
    Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D (Stable.ConfigurationLocus.configurationHilbertRank D P)

def coefficientMap : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced →+*
    Γ((base R i j D P hP g Pm Pi N).left, ⊤) :=
  (toCoefficientChart R i j D P hP g Pm Pi N).left.appTop.hom.comp
    (Scheme.ΓSpecIso (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced))).inv.hom

def markedPoint (k : Fin m) : Over.mk (𝟙 (base R i j D P hP g Pm Pi N).left) ⟶
    Projective.ProjectivePresentations.projectiveSpaceOver (base R i j D P hP g Pm Pi N).left
      (basePresentation R i j D P hP g Pm Pi N).dimension :=
  Balanced.FrameChartProjectivePoints.balancedFrameChartProjectivePoint R i j.frame j.additional j.coordinate j.exponent
    j.complement j.balanced j.complete (base R i j D P hP g Pm Pi N).left
    (coefficientMap R i j D P hP g Pm Pi N) k

variable (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))

def parameter : Over (Spec (.of R)) :=
  PrescribedLevelAmbientParameter.prescribedFullLevelAmbientParameter (base R i j D P hP g Pm Pi N)
    (baseFamily R i j D P hP g Pm Pi N).abelian
    (baseFamily R i j D P hP g Pm Pi N).level
    (basePresentation R i j D P hP g Pm Pi N) labels (markedPoint R i j D P hP g Pm Pi N)

def inclusion : parameter R i j D P hP g Pm Pi N labels ⟶ base R i j D P hP g Pm Pi N :=
  PrescribedLevelAmbientParameter.prescribedFullLevelAmbientParameterInclusion (base R i j D P hP g Pm Pi N)
    (baseFamily R i j D P hP g Pm Pi N).abelian
    (baseFamily R i j D P hP g Pm Pi N).level
    (basePresentation R i j D P hP g Pm Pi N) labels (markedPoint R i j D P hP g Pm Pi N)

instance inclusion_closed : IsClosedImmersion (inclusion R i j D P hP g Pm Pi N labels).left :=
  PrescribedLevelAmbientParameter.prescribedFullLevelAmbientParameterInclusion_closed (base R i j D P hP g Pm Pi N)
    (baseFamily R i j D P hP g Pm Pi N).abelian
    (baseFamily R i j D P hP g Pm Pi N).level
    (basePresentation R i j D P hP g Pm Pi N) labels (markedPoint R i j D P hP g Pm Pi N)

def quasiProjective : Projective.ProjectivePresentations.QuasiProjectivePresentation (parameter R i j D P hP g Pm Pi N labels) :=
  (baseQuasiProjective R i j D P hP g Pm Pi N).ofClosedImmersion
    (inclusion R i j D P hP g Pm Pi N labels)

def family : Level.Data.AbelianSchemeWithFullLevel g N (parameter R i j D P hP g Pm Pi N labels).left :=
  PrescribedLevelAmbientParameter.prescribedFullLevelAmbientUniversalFamily (base R i j D P hP g Pm Pi N)
    (baseFamily R i j D P hP g Pm Pi N).abelian
    (baseFamily R i j D P hP g Pm Pi N).level
    (basePresentation R i j D P hP g Pm Pi N) labels (markedPoint R i j D P hP g Pm Pi N)

def presentation : Projective.ProjectivePresentations.ProjectivePresentation (family R i j D P hP g Pm Pi N labels).abelian.scheme :=
  (basePresentation R i j D P hP g Pm Pi N).baseChange
    (inclusion R i j D P hP g Pm Pi N labels).left

def pointEquiv (T : Over (Spec (.of R))) :
    (T ⟶ parameter R i j D P hP g Pm Pi N labels) ≃
      {c : T ⟶ base R i j D P hP g Pm Pi N //
        PrescribedLevelAmbientParameter.PrescribedFullLevelAmbientAt (base R i j D P hP g Pm Pi N)
          (baseFamily R i j D P hP g Pm Pi N).abelian
          (baseFamily R i j D P hP g Pm Pi N).level
          (basePresentation R i j D P hP g Pm Pi N) labels
          (markedPoint R i j D P hP g Pm Pi N) c.left} :=
  PrescribedLevelAmbientParameter.prescribedFullLevelAmbientParameterPointEquiv (base R i j D P hP g Pm Pi N)
    (baseFamily R i j D P hP g Pm Pi N).abelian
    (baseFamily R i j D P hP g Pm Pi N).level
    (basePresentation R i j D P hP g Pm Pi N) labels (markedPoint R i j D P hP g Pm Pi N) T

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelParameter.StableHilbertLevel
