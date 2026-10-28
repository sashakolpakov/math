import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PrescribedFrameCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Abelian.ZeroNormalizedBundle
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationTensorTwisting
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FramePointBaseChange

/-! # Polarization Frame Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationFrameCoverage

noncomputable section

/-! The original stable polarization charts retain their actual
ordered marked frame and prescribed normalized graph-power class. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
universe u
namespace StableHilbertCoverage

private theorem frame_zeroNormalized_class_congr
    {S : Scheme.{u}} {g : ℕ} (A : Abelian.Schemes.AbelianScheme g S)
    (L M : Line.Bundles.LineBundle A.scheme.left)
    (h : Line.Bundles.LineBundle.classOf L = Line.Bundles.LineBundle.classOf M) :
    Line.Bundles.LineBundle.classOf (A.zeroNormalizedBundle L) =
      Line.Bundles.LineBundle.classOf (A.zeroNormalizedBundle M) :=
  (Line.Bundles.LineBundle.classOf_sectionNormalized A.scheme.hom η[A.scheme].left L).trans
    ((congrArg (Line.Bundles.LineBundle.sectionNormalizeClass A.scheme.hom η[A.scheme].left) h).trans
      (Line.Bundles.LineBundle.classOf_sectionNormalized A.scheme.hom η[A.scheme].left M).symm)

private theorem frame_projectiveSectionBaseChange_congr
    {S T : Scheme.{u}} {n : ℕ}
    {s t : Over.mk (𝟙 S) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n}
    (h : s = t) (f : T ⟶ S) :
    Projective.SectionBaseChange.projectiveSectionBaseChange s f = Projective.SectionBaseChange.projectiveSectionBaseChange t f :=
  congrArg (fun a : Over.mk (𝟙 S) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n =>
    Projective.SectionBaseChange.projectiveSectionBaseChange a f) h

end StableHilbertCoverage

namespace StableHilbertLevel
variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))

def familyCoefficientMap : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced →+*
    Γ((LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels).left, ⊤) :=
  (LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels).left.appTop.hom.comp
    (LevelParameter.StableHilbertLevel.coefficientMap R i j D H hH g Hm Hi N)

theorem presentation_markedPoint (z : Fin m) :
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint
      (Over.mk (𝟙 (LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels).left))
      (LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).abelian
      (LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).level
      (LevelParameter.StableHilbertLevel.presentation R i j D H hH g Hm Hi N labels) (labels z) =
    Balanced.FrameChartProjectivePoints.balancedFrameChartProjectivePoint R i j.frame j.additional j.coordinate j.exponent
      j.complement j.balanced j.complete (LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels).left
      (familyCoefficientMap R i j D H hH g Hm Hi N labels) z := by
  let Z := LevelParameter.StableHilbertLevel.base R i j D H hH g Hm Hi N
  let F := LevelParameter.StableHilbertLevel.baseFamily R i j D H hH g Hm Hi N
  let P := LevelParameter.StableHilbertLevel.basePresentation R i j D H hH g Hm Hi N
  let q := LevelParameter.StableHilbertLevel.markedPoint R i j D H hH g Hm Hi N
  let c := (LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels).left
  have hp := PrescribedLevelAmbientParameter.prescribedFullLevelAmbientParameter_universal Z F.abelian F.level P labels q
  exact (PrescribedFrameCoverage.StableHilbertCoverage.prescribedPullback_markedPoint Z F.abelian F.level P labels q c hp z).trans
    (Balanced.FramePointBaseChange.balancedFrameChartProjectivePoint_baseChange R i j.frame j.additional
      j.coordinate j.exponent j.complement j.balanced j.complete
      (LevelParameter.StableHilbertLevel.coefficientMap R i j D H hH g Hm Hi N) c z)

theorem presentation_standardFrame :
    ∀ k, Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint
      (Over.mk (𝟙 (LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels).left))
      (LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).abelian
      (LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).level
      (LevelParameter.StableHilbertLevel.presentation R i j D H hH g Hm Hi N labels) (labels (j.frame k)) =
        Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint (LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels).left n k := by
  let Z := LevelParameter.StableHilbertLevel.base R i j D H hH g Hm Hi N
  let F := LevelParameter.StableHilbertLevel.baseFamily R i j D H hH g Hm Hi N
  let P := LevelParameter.StableHilbertLevel.basePresentation R i j D H hH g Hm Hi N
  let q := LevelParameter.StableHilbertLevel.markedPoint R i j D H hH g Hm Hi N
  have hq : ∀ k, q (j.frame k) = Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint Z.left n k :=
    (Balanced.FrameChartProjectivePoints.balancedFrameChartProjectivePoint_normalizes R i j.frame j.additional j.coordinate
      j.exponent j.complement j.balanced j.complete
      ((Frame.ChartDenominators.frameDiscriminantExponent_le_chart j.frame j.additional j.coordinate).trans j.frame_le)
      Z.left (LevelParameter.StableHilbertLevel.coefficientMap R i j D H hH g Hm Hi N)).2
  exact PrescribedFrameCoverage.StableHilbertCoverage.prescribedPullback_standardFrame Z F.abelian F.level P labels q
    (LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels).left
    (PrescribedLevelAmbientParameter.prescribedFullLevelAmbientParameter_universal Z F.abelian F.level P labels q) j.frame hq

end StableHilbertLevel

namespace StableHilbertPolarization
variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)
    (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)

local notation "M" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ
local notation "A" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.universalFamily R i j D H hH g Hm Hi N labels qR d hd δ hδ
local notation "P" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.universalPresentation R i j D H hH g Hm Hi N labels qR d hd δ hδ
local notation "F₀" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.baseFamily R i j D H hH g Hm Hi N labels
local notation "P₀" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.basePresentation R i j D H hH g Hm Hi N labels
local notation "p" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ

def universalCoefficientMap : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced →+*
    Γ((M).left, ⊤) :=
  (p).left.appTop.hom.comp (StableHilbertLevel.familyCoefficientMap R i j D H hH g Hm Hi N labels)

theorem universalPresentation_markedPoint (z : Fin m) :
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 (M).left)) (A).abelian (A).level (P) (labels z) =
      Balanced.FrameChartProjectivePoints.balancedFrameChartProjectivePoint R i j.frame j.additional j.coordinate j.exponent
        j.complement j.balanced j.complete (M).left
        (universalCoefficientMap R i j D H hH g Hm Hi N labels qR d hd δ hδ) z := by
  have hm := StableHilbertLevel.presentation_markedPoint R i j D H hH g Hm Hi N labels z
  exact (PrescribedFrameCoverage.StableHilbertCoverage.fullLevelMarkedPoint_pullback_eq
    (Over.mk (𝟙 (PolarizationParameter.StableHilbertPolarization.base R i j D H hH g Hm Hi N labels).left))
    (F₀).abelian (F₀).level (P₀) (p).left (labels z)).trans
      ((StableHilbertCoverage.frame_projectiveSectionBaseChange_congr (n := n) hm (p).left).trans
        (Balanced.FramePointBaseChange.balancedFrameChartProjectivePoint_baseChange R i j.frame j.additional j.coordinate
          j.exponent j.complement j.balanced j.complete
          (StableHilbertLevel.familyCoefficientMap R i j D H hH g Hm Hi N labels) (p).left z))

theorem universalPresentation_standardFrame :
    ∀ k, Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 (M).left)) (A).abelian (A).level (P)
      (labels (j.frame k)) = Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint (M).left n k :=
  PresentationCompleteness.StableHilbertCoverage.fullLevelStandardFrame_baseChange (F₀).abelian (F₀).level (P₀)
    (fun k => labels (j.frame k))
    (StableHilbertLevel.presentation_standardFrame R i j D H hH g Hm Hi N labels) (p).left

theorem universalPresentation_normalizedPowerClass :
    Line.Bundles.LineBundle.classOf ((A).abelian.zeroNormalizedBundle (P).ampleLineBundle) =
      Line.Bundles.LineBundle.classOf ((A).graphBundle.tensorPower d) := by
  let π := pullback.fst (F₀).abelian.scheme.hom (p).left
  have hL := StableHilbertCoverage.frame_zeroNormalized_class_congr (A).abelian (P).ampleLineBundle
    ((P₀).ampleLineBundle.pullback π) (Quotient.sound ⟨(P₀).baseChangeTwistingBundleIso (p).left⟩)
  have hn : Line.Bundles.LineBundle.classOf (((F₀).abelian.zeroNormalizedBundle (P₀).ampleLineBundle).pullback π) =
      Line.Bundles.LineBundle.classOf ((A).abelian.zeroNormalizedBundle ((P₀).ampleLineBundle.pullback π)) :=
    Quotient.sound ⟨(F₀).abelian.zeroNormalizedBundle_baseChangeIso (P₀).ampleLineBundle (p).left⟩
  have hP : Line.Bundles.LineBundle.classOf (((F₀).abelian.zeroNormalizedBundle (P₀).ampleLineBundle).pullback π) =
      Line.Bundles.LineBundle.classOf ((A).graphBundle.tensorPower d) :=
    Quotient.sound ⟨Rational.GlobalGraphPowerParameter.RationalGlobalGraphPowerLocus.universalPowerIso
      (PolarizationParameter.StableHilbertPolarization.base R i j D H hH g Hm Hi N labels) (F₀) (P₀)
      ((PolarizationParameter.StableHilbertPolarization.base R i j D H hH g Hm Hi N labels).hom ≫ qR) d hd δ hδ⟩
  exact hL.trans (hn.symm.trans hP)

end StableHilbertPolarization

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationFrameCoverage
