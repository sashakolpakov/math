import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.LevelParameter
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Balanced.FramePointBaseChange

/-! # Marked Point Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.MarkedPointNaturality.StableHilbertLevel

noncomputable section

/-! The prescribed marks of a stable Hilbert chart depend only on its
actual configuration point, including after arbitrary test pullbacks. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
    (D : ℕ) (P : Polynomial ℚ)
    (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
    (g : ℕ) (Pm Pi : Polynomial ℚ) (N : ℕ) [NeZero N]

theorem markedPoint_eq_baseChange (k : Fin m) :
    LevelParameter.StableHilbertLevel.markedPoint R i j D P hP g Pm Pi N k =
      Projective.SectionBaseChange.projectiveSectionBaseChange
        (Balanced.FrameChartProjectivePoints.balancedFrameChartUniversalPoint R i j.frame j.additional j.coordinate j.exponent
          j.complement j.balanced j.complete k)
        (LevelParameter.StableHilbertLevel.toCoefficientChart R i j D P hP g Pm Pi N).left :=
  (Balanced.FramePointBaseChange.balancedFrameChartUniversalPoint_baseChange R i j.frame j.additional j.coordinate j.exponent
    j.complement j.balanced j.complete (LevelParameter.StableHilbertLevel.toCoefficientChart R i j D P hP g Pm Pi N).left k).symm

theorem markedPoint_baseChange_eq_of_toChart_eq
    {T : Over (Spec (.of R))}
    (a b : T ⟶ LevelParameter.StableHilbertLevel.base R i j D P hP g Pm Pi N)
    (h : a ≫ LevelParameter.StableHilbertLevel.toChart R i j D P hP g Pm Pi N = b ≫ LevelParameter.StableHilbertLevel.toChart R i j D P hP g Pm Pi N)
    (k : Fin m) :
    Projective.SectionBaseChange.projectiveSectionBaseChange (LevelParameter.StableHilbertLevel.markedPoint R i j D P hP g Pm Pi N k) a.left =
      Projective.SectionBaseChange.projectiveSectionBaseChange (LevelParameter.StableHilbertLevel.markedPoint R i j D P hP g Pm Pi N k) b.left := by
  let q := Stable.ConfigurationLocus.stableConfigurationHilbertRankInclusion R i j D P ≫
    Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D (Stable.ConfigurationLocus.configurationHilbertRank D P)
  have hq : a ≫ LevelParameter.StableHilbertLevel.toCoefficientChart R i j D P hP g Pm Pi N =
      b ≫ LevelParameter.StableHilbertLevel.toCoefficientChart R i j D P hP g Pm Pi N :=
    (Category.assoc a (LevelParameter.StableHilbertLevel.toChart R i j D P hP g Pm Pi N) q).symm.trans
      ((congrArg (fun z => z ≫ q) h).trans
        (Category.assoc b (LevelParameter.StableHilbertLevel.toChart R i j D P hP g Pm Pi N) q))
  let s := Balanced.FrameChartProjectivePoints.balancedFrameChartUniversalPoint R i j.frame j.additional j.coordinate j.exponent
    j.complement j.balanced j.complete k
  have he := markedPoint_eq_baseChange R i j D P hP g Pm Pi N k
  exact (congrArg (fun z => Projective.SectionBaseChange.projectiveSectionBaseChange z a.left) he).trans
    ((Projective.SectionBaseChange.projectiveSectionBaseChange_eq_of_comp_eq s
      (LevelParameter.StableHilbertLevel.toCoefficientChart R i j D P hP g Pm Pi N).left a.left b.left
      (congrArg Over.Hom.left hq)).trans
      (congrArg (fun z => Projective.SectionBaseChange.projectiveSectionBaseChange z b.left) he).symm)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.MarkedPointNaturality.StableHilbertLevel
