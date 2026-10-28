import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationMarkedPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter

/-! # Graph Power Marked Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerMarkedPoints

noncomputable section

/-! The ordered marked sections on the factory's actual stable charts,
including their values after arbitrary base change. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

private theorem markedSectionBaseChange_congr
    {S T : Scheme.{u}} {n : ℕ}
    {s t : Over.mk (𝟙 S) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n}
    (h : s = t) (f : T ⟶ S) :
    Projective.SectionBaseChange.projectiveSectionBaseChange s f = Projective.SectionBaseChange.projectiveSectionBaseChange t f :=
  congrArg (fun q : Over.mk (𝟙 S) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n =>
    Projective.SectionBaseChange.projectiveSectionBaseChange q f) h

private theorem markedSectionBaseChange_comp
    {S T U : Scheme.{u}} {n : ℕ}
    (s : Over.mk (𝟙 S) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)
    (t : Over.mk (𝟙 T) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver T n)
    (r : Over.mk (𝟙 U) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver U n)
    (f : T ⟶ S) (a : U ⟶ T)
    (hr : r = Projective.SectionBaseChange.projectiveSectionBaseChange t a)
    (ht : t = Projective.SectionBaseChange.projectiveSectionBaseChange s f) :
    r = Projective.SectionBaseChange.projectiveSectionBaseChange s (a ≫ f) :=
  hr.trans ((markedSectionBaseChange_congr ht a).trans
    (Projective.SectionBaseChange.projectiveSectionBaseChange_comp s f a))

namespace StableHilbertGraphPower
variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m)
    (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (d : ℕ) (δ : Fin g → ℕ) (Φ : GraphPower.LocusPresentation.GraphPowerLocusFactory R g N d δ)

local notation "M" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ
local notation "F" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.universalFamily R i j D H hH g Hm Hi N labels d δ Φ
local notation "P" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.universalPresentation R i j D H hH g Hm Hi N labels d δ Φ
local notation "p" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.inclusion R i j D H hH g Hm Hi N labels d δ Φ
local notation "B" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.base R i j D H hH g Hm Hi N labels
local notation "F₀" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.baseFamily R i j D H hH g Hm Hi N labels
local notation "P₀" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerParameter.StableHilbertGraphPower.basePresentation R i j D H hH g Hm Hi N labels

def toCoefficientChart : M ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j :=
  p ≫ PolarizationMarkedPoints.StableHilbertFullLevel.parameterToCoefficientChart R i j D H hH g Hm Hi N labels

theorem universalPresentation_markedPoint_baseChange (k : Fin m) :
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 (M).left)) (F).abelian (F).level P (labels k) =
      Projective.SectionBaseChange.projectiveSectionBaseChange
        (Balanced.FrameChartProjectivePoints.balancedFrameChartUniversalPoint R i j.frame j.additional j.coordinate
          j.exponent j.complement j.balanced j.complete k)
        (toCoefficientChart R i j D H hH g Hm Hi N labels d δ Φ).left := by
  let c := PolarizationMarkedPoints.StableHilbertFullLevel.parameterToCoefficientChart R i j D H hH g Hm Hi N labels
  let s := Balanced.FrameChartProjectivePoints.balancedFrameChartUniversalPoint R i j.frame j.additional j.coordinate
    j.exponent j.complement j.balanced j.complete k
  have h₁ := PrescribedFrameCoverage.StableHilbertCoverage.fullLevelMarkedPoint_pullback_eq
    (Over.mk (𝟙 (B).left)) (F₀).abelian (F₀).level P₀ (p).left (labels k)
  have h₂ := PolarizationMarkedPoints.StableHilbertFullLevel.presentation_markedPoint_baseChange R i j D H hH g Hm Hi N labels k
  exact markedSectionBaseChange_comp (n := n) s _ _ c.left (p).left h₁ h₂

theorem universalPresentation_scalarMark (k : Fin m) :
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 (M).left)) (F).abelian (F).level P (labels k) =
      Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint
        (Stable.BalancedOrbitEquality.StableHilbertCoverage.normalizedVectors R i j M
          (toCoefficientChart R i j D H hH g Hm Hi N labels d δ Φ) k)
        (Stable.BalancedProjectivePoints.StableHilbertCoverage.normalizedVectors_cover R i j M
          (toCoefficientChart R i j D H hH g Hm Hi N labels d δ Φ) k) :=
  (universalPresentation_markedPoint_baseChange R i j D H hH g Hm Hi N labels d δ Φ k).trans
    (Stable.BalancedProjectivePoints.StableHilbertCoverage.normalizedProjectivePoint_baseChange R i j M
      (toCoefficientChart R i j D H hH g Hm Hi N labels d δ Φ) k)

theorem universalPresentation_scalarMarkAt {T : Over (Spec (.of R))}
    (a : T ⟶ M) (k : Fin m) :
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 T.left)) ((F).pullback a.left).abelian
      ((F).pullback a.left).level ((P).baseChange a.left) (labels k) =
      Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint
        (Stable.BalancedOrbitEquality.StableHilbertCoverage.normalizedVectors R i j T
          (a ≫ toCoefficientChart R i j D H hH g Hm Hi N labels d δ Φ) k)
        (Stable.BalancedProjectivePoints.StableHilbertCoverage.normalizedVectors_cover R i j T
          (a ≫ toCoefficientChart R i j D H hH g Hm Hi N labels d δ Φ) k) := by
  let c := toCoefficientChart R i j D H hH g Hm Hi N labels d δ Φ
  let s := Balanced.FrameChartProjectivePoints.balancedFrameChartUniversalPoint R i j.frame j.additional j.coordinate
    j.exponent j.complement j.balanced j.complete k
  have h₁ := PrescribedFrameCoverage.StableHilbertCoverage.fullLevelMarkedPoint_pullback_eq (Over.mk (𝟙 (M).left))
    (F).abelian (F).level P a.left (labels k)
  have h₂ := universalPresentation_markedPoint_baseChange R i j D H hH g Hm Hi N labels d δ Φ k
  have h := markedSectionBaseChange_comp (n := n) s _ _ c.left a.left h₁ h₂
  exact h.trans
    (Stable.BalancedProjectivePoints.StableHilbertCoverage.normalizedProjectivePoint_baseChange R i j T (a ≫ c) k)

end StableHilbertGraphPower

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerMarkedPoints
