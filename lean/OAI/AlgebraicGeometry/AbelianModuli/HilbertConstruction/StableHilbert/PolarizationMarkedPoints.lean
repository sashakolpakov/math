import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.MarkedPointNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedProjectivePoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SectionEquations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PrescribedFrameCoverage

/-! # Polarization Marked Points -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationMarkedPoints

noncomputable section

/-! Every ordered full-level section of the original stable polarization
family is its specified normalized configuration point. These are
equalities of actual projective sections, including on arbitrary tests. -/

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

theorem prescribedPullback_markedPoint
    {S T : Scheme.{u}} (Z : Over S) [IsLocallyNoetherian Z.left]
    {g N m : ℕ} (A : Abelian.Schemes.AbelianScheme g Z.left) (level : A.FullLevel N)
    (P : Projective.ProjectivePresentations.ProjectivePresentation A.scheme)
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (q : Fin m → (Over.mk (𝟙 Z.left) ⟶ Projective.ProjectivePresentations.projectiveSpaceOver Z.left P.dimension))
    (f : T ⟶ Z.left) (h : PrescribedLevelAmbientParameter.PrescribedFullLevelAmbientAt Z A level P labels q f)
    (k : Fin m) :
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 T)) (A.pullback f) (level.pullback f)
      (P.baseChange f) (labels k) = Projective.SectionBaseChange.projectiveSectionBaseChange (q k) f :=
  PrescribedFrameCoverage.StableHilbertCoverage.prescribedPullback_markedPoint Z A level P labels q f h k

namespace StableHilbertFullLevel
variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D H) H)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))

def parameterToCoefficientChart : LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels ⟶
    Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j :=
  LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels ≫ LevelParameter.StableHilbertLevel.toCoefficientChart R i j D H hH g Hm Hi N

theorem presentation_markedPoint_baseChange (k : Fin m) :
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint
      (Over.mk (𝟙 (LevelParameter.StableHilbertLevel.parameter R i j D H hH g Hm Hi N labels).left))
      (LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).abelian
      (LevelParameter.StableHilbertLevel.family R i j D H hH g Hm Hi N labels).level
      (LevelParameter.StableHilbertLevel.presentation R i j D H hH g Hm Hi N labels) (labels k) =
    Projective.SectionBaseChange.projectiveSectionBaseChange
      (Balanced.FrameChartProjectivePoints.balancedFrameChartUniversalPoint R i j.frame j.additional j.coordinate
        j.exponent j.complement j.balanced j.complete k)
      (parameterToCoefficientChart R i j D H hH g Hm Hi N labels).left := by
  let Z := LevelParameter.StableHilbertLevel.base R i j D H hH g Hm Hi N
  let F := LevelParameter.StableHilbertLevel.baseFamily R i j D H hH g Hm Hi N
  let P := LevelParameter.StableHilbertLevel.basePresentation R i j D H hH g Hm Hi N
  let q := LevelParameter.StableHilbertLevel.markedPoint R i j D H hH g Hm Hi N
  let p := LevelParameter.StableHilbertLevel.inclusion R i j D H hH g Hm Hi N labels
  let c := LevelParameter.StableHilbertLevel.toCoefficientChart R i j D H hH g Hm Hi N
  let s := Balanced.FrameChartProjectivePoints.balancedFrameChartUniversalPoint R i j.frame j.additional j.coordinate
    j.exponent j.complement j.balanced j.complete k
  have h₁ := prescribedPullback_markedPoint Z F.abelian F.level P labels q p.left
    (PrescribedLevelAmbientParameter.prescribedFullLevelAmbientParameter_universal Z F.abelian F.level P labels q) k
  have h₂ : q k = Projective.SectionBaseChange.projectiveSectionBaseChange s c.left :=
    MarkedPointNaturality.StableHilbertLevel.markedPoint_eq_baseChange R i j D H hH g Hm Hi N k
  exact h₁.trans ((markedSectionBaseChange_congr (n := n) h₂ p.left).trans
    (Projective.SectionBaseChange.projectiveSectionBaseChange_comp s c.left p.left))

end StableHilbertFullLevel

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
local notation "F" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.universalFamily R i j D H hH g Hm Hi N labels qR d hd δ hδ
local notation "P" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.universalPresentation R i j D H hH g Hm Hi N labels qR d hd δ hδ
local notation "p" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.inclusion R i j D H hH g Hm Hi N labels qR d hd δ hδ
local notation "B" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.base R i j D H hH g Hm Hi N labels
local notation "F₀" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.baseFamily R i j D H hH g Hm Hi N labels
local notation "P₀" => OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationParameter.StableHilbertPolarization.basePresentation R i j D H hH g Hm Hi N labels

def toCoefficientChart : M ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j :=
  p ≫ StableHilbertFullLevel.parameterToCoefficientChart R i j D H hH g Hm Hi N labels

theorem universalPresentation_markedPoint_baseChange (k : Fin m) :
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 (M).left)) (F).abelian (F).level P (labels k) =
      Projective.SectionBaseChange.projectiveSectionBaseChange
        (Balanced.FrameChartProjectivePoints.balancedFrameChartUniversalPoint R i j.frame j.additional j.coordinate
          j.exponent j.complement j.balanced j.complete k)
        (toCoefficientChart R i j D H hH g Hm Hi N labels qR d hd δ hδ).left := by
  let c := StableHilbertFullLevel.parameterToCoefficientChart R i j D H hH g Hm Hi N labels
  let s := Balanced.FrameChartProjectivePoints.balancedFrameChartUniversalPoint R i j.frame j.additional j.coordinate
    j.exponent j.complement j.balanced j.complete k
  have h₁ := PrescribedFrameCoverage.StableHilbertCoverage.fullLevelMarkedPoint_pullback_eq
    (Over.mk (𝟙 (B).left)) (F₀).abelian (F₀).level P₀ (p).left (labels k)
  have h₂ := StableHilbertFullLevel.presentation_markedPoint_baseChange R i j D H hH g Hm Hi N labels k
  exact markedSectionBaseChange_comp (n := n) s _ _ c.left (p).left h₁ h₂

theorem universalPresentation_scalarMark (k : Fin m) :
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 (M).left)) (F).abelian (F).level P (labels k) =
      Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint
        (Stable.BalancedOrbitEquality.StableHilbertCoverage.normalizedVectors R i j M
          (toCoefficientChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) k)
        (Stable.BalancedProjectivePoints.StableHilbertCoverage.normalizedVectors_cover R i j M
          (toCoefficientChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) k) :=
  (universalPresentation_markedPoint_baseChange R i j D H hH g Hm Hi N labels qR d hd δ hδ k).trans
    (Stable.BalancedProjectivePoints.StableHilbertCoverage.normalizedProjectivePoint_baseChange R i j M
      (toCoefficientChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) k)

theorem universalPresentation_scalarMarkAt {T : Over (Spec (.of R))}
    (a : T ⟶ M) (k : Fin m) :
    Normalized.LevelFrameParameter.fullLevelMarkedProjectivePoint (Over.mk (𝟙 T.left)) ((F).pullback a.left).abelian
      ((F).pullback a.left).level ((P).baseChange a.left) (labels k) =
      Family.SectionProjectiveCoordinates.scalarCoordinateProjectivePoint
        (Stable.BalancedOrbitEquality.StableHilbertCoverage.normalizedVectors R i j T
          (a ≫ toCoefficientChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) k)
        (Stable.BalancedProjectivePoints.StableHilbertCoverage.normalizedVectors_cover R i j T
          (a ≫ toCoefficientChart R i j D H hH g Hm Hi N labels qR d hd δ hδ) k) := by
  let c := toCoefficientChart R i j D H hH g Hm Hi N labels qR d hd δ hδ
  let s := Balanced.FrameChartProjectivePoints.balancedFrameChartUniversalPoint R i j.frame j.additional j.coordinate
    j.exponent j.complement j.balanced j.complete k
  have h₁ := PrescribedFrameCoverage.StableHilbertCoverage.fullLevelMarkedPoint_pullback_eq (Over.mk (𝟙 (M).left))
    (F).abelian (F).level P a.left (labels k)
  have h₂ := universalPresentation_markedPoint_baseChange R i j D H hH g Hm Hi N labels qR d hd δ hδ k
  have h := markedSectionBaseChange_comp (n := n) s _ _ c.left a.left h₁ h₂
  exact h.trans
    (Stable.BalancedProjectivePoints.StableHilbertCoverage.normalizedProjectivePoint_baseChange R i j T (a ≫ c) k)

end StableHilbertPolarization

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationMarkedPoints
