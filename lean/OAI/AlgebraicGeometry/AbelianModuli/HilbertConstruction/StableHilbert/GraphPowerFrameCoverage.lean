import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationFrameCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter

/-! # Graph Power Frame Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerFrameCoverage

noncomputable section

/-! The marked frame and normalized graph-power class on the stable
charts obtained from a graph-power locus factory. -/

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

namespace StableHilbertGraphPower
variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)
    (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (d : ℕ) (δ : Fin g → ℕ) (Φ : GraphPower.LocusPresentation.GraphPowerLocusFactory R g N d δ)

local notation "M" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ
local notation "A" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.universalFamily R i j D H hH g Hm Hi N labels d δ Φ
local notation "P" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.universalPresentation R i j D H hH g Hm Hi N labels d δ Φ
local notation "F₀" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.baseFamily R i j D H hH g Hm Hi N labels
local notation "P₀" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.basePresentation R i j D H hH g Hm Hi N labels
local notation "p" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ

def universalCoefficientMap : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced →+*
    Γ((M).left, ⊤) :=
  (p).left.appTop.hom.comp (PolarizationFrameCoverage.StableHilbertLevel.familyCoefficientMap R i j D H hH g Hm Hi N labels)

theorem universalPresentation_markedPoint (z : Fin m) :
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 (M).left)) (A).abelian (A).level (P) (labels z) =
      Balanced.FrameChartProjectivePoints.balancedFrameChartProjectivePoint R i j.frame j.additional j.coordinate j.exponent
        j.complement j.balanced j.complete (M).left
        (universalCoefficientMap R i j D H hH g Hm Hi N labels d δ Φ) z := by
  have hm := PolarizationFrameCoverage.StableHilbertLevel.presentation_markedPoint R i j D H hH g Hm Hi N labels z
  exact (PrescribedFrameCoverage.StableHilbertCoverage.fullLevelMarkedPoint_pullback_eq
    (Over.mk (𝟙 (GraphPowerParameter.StableHilbertGraphPower.base R i j D H hH g Hm Hi N labels).left))
    (F₀).abelian (F₀).level (P₀) (p).left (labels z)).trans
      ((StableHilbertCoverage.frame_projectiveSectionBaseChange_congr (n := n) hm (p).left).trans
        (Balanced.FramePointBaseChange.balancedFrameChartProjectivePoint_baseChange R i j.frame j.additional j.coordinate
          j.exponent j.complement j.balanced j.complete
          (PolarizationFrameCoverage.StableHilbertLevel.familyCoefficientMap R i j D H hH g Hm Hi N labels) (p).left z))

theorem universalPresentation_standardFrame :
    ∀ k, Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 (M).left)) (A).abelian (A).level (P)
      (labels (j.frame k)) = Scalar.CoordinateProjectivePoints.standardBasisProjectivePoint (M).left n k :=
  PresentationCompleteness.StableHilbertCoverage.fullLevelStandardFrame_baseChange (F₀).abelian (F₀).level (P₀)
    (fun k => labels (j.frame k))
    (PolarizationFrameCoverage.StableHilbertLevel.presentation_standardFrame R i j D H hH g Hm Hi N labels) (p).left

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
    Quotient.sound ⟨(GraphPowerParameter.StableHilbertGraphPower.locus R i j D H hH g Hm Hi N labels d δ Φ).universalPowerIso⟩
  exact hL.trans (hn.symm.trans hP)

end StableHilbertGraphPower

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerFrameCoverage
