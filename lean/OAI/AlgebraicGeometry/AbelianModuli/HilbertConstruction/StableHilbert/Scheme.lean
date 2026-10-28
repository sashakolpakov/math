import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.ChartPullbacks
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.MonoFamilyGluing

/-! # Scheme -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.Scheme

noncomputable section

/-! Stable configuration Hilbert loci glue to an actual scheme
mapping monomorphically to the global polynomial rank scheme. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.MonoFamilyGluing
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] [IsNoetherianRing R]
variable {n m : ℕ} (i : Fin m) (D : ℕ) (P : Polynomial ℚ)
variable (hP : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n D P) P)
variable (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ D)

include hP hD in
theorem stableHilbertIntersectionOpens :
    ∀ j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m,
      IsOpenImmersion (pullback.fst (ChartPullbacks.stableHilbertChartToRank R i j D P) (ChartPullbacks.stableHilbertChartToRank R i k D P)).left :=
  fun j k => ChartPullbacks.stableHilbertChartPullback_fst_open R i j k D P hP hD

def stableHilbertGlueData : Scheme.GlueData := by
  letI := stableHilbertIntersectionOpens R i D P hP hD
  exact HilbertScheme.Presentations.Relative.MonoFamilyGluing.relativeMonoFamilyGlueData (Stable.PolynomialRankScheme.stablePolynomialRankOver R i D (Stable.ConfigurationLocus.configurationHilbertRank D P))
    (fun j : ULift.{u} (Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) => Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j.down D P) (fun j : ULift.{u} (Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) => ChartPullbacks.stableHilbertChartToRank R i j.down D P)

def stableHilbertScheme : Scheme.{u} := (stableHilbertGlueData R i D P hP hD).glued

def stableHilbertChart (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P).left ⟶ stableHilbertScheme R i D P hP hD :=
  (stableHilbertGlueData R i D P hP hD).ι (ULift.up j)

instance stableHilbertChart_open (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    IsOpenImmersion (stableHilbertChart R i D P hP hD j) :=
  Scheme.GlueData.ι_isOpenImmersion (stableHilbertGlueData R i D P hP hD) (ULift.up j)

def stableHilbertRankParameter : stableHilbertScheme R i D P hP hD ⟶
    (Stable.PolynomialRankScheme.stablePolynomialRankOver R (n := n) i D (Stable.ConfigurationLocus.configurationHilbertRank D P)).left := by
  letI := stableHilbertIntersectionOpens R i D P hP hD
  exact HilbertScheme.Presentations.Relative.MonoFamilyGluing.relativeMonoFamilyParameter (Stable.PolynomialRankScheme.stablePolynomialRankOver R i D (Stable.ConfigurationLocus.configurationHilbertRank D P))
    (fun j : ULift.{u} (Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) => Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j.down D P) (fun j : ULift.{u} (Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) => ChartPullbacks.stableHilbertChartToRank R i j.down D P)

theorem stableHilbertChart_rankParameter (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    stableHilbertChart R i D P hP hD j ≫ stableHilbertRankParameter R i D P hP hD =
      (ChartPullbacks.stableHilbertChartToRank R i j D P).left := by
  let := stableHilbertIntersectionOpens R i D P hP hD
  exact HilbertScheme.Presentations.Relative.MonoFamilyGluing.relativeMonoFamilyChart_parameter _ _ _ (ULift.up j)

instance stableHilbertRankParameter_mono : Mono (stableHilbertRankParameter R i D P hP hD) := by
  let := stableHilbertIntersectionOpens R i D P hP hD
  exact HilbertScheme.Presentations.Relative.MonoFamilyGluing.relativeMonoFamilyParameter_mono _ _ _

def stableHilbertOver : Over (Spec (.of R)) :=
  Over.mk (stableHilbertRankParameter R i D P hP hD ≫
    (Stable.PolynomialRankScheme.stablePolynomialRankOver R (n := n) i D (Stable.ConfigurationLocus.configurationHilbertRank D P)).hom)

def stableHilbertRankParameterOver : stableHilbertOver R i D P hP hD ⟶
    Stable.PolynomialRankScheme.stablePolynomialRankOver R (n := n) i D (Stable.ConfigurationLocus.configurationHilbertRank D P) :=
  Over.homMk (stableHilbertRankParameter R i D P hP hD) rfl

instance stableHilbertRankParameterOver_mono : Mono (stableHilbertRankParameterOver R i D P hP hD) :=
  by
    have : Mono (stableHilbertRankParameterOver R i D P hP hD).left :=
      inferInstanceAs (Mono (stableHilbertRankParameter R i D P hP hD))
    exact Over.mono_of_mono_left _

def stableHilbertChartOver (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P ⟶ stableHilbertOver R i D P hP hD :=
  Over.homMk (stableHilbertChart R i D P hP hD j) (by
    change stableHilbertChart R i D P hP hD j ≫ (stableHilbertRankParameter R i D P hP hD ≫ _) = _
    rw [← Category.assoc, stableHilbertChart_rankParameter]
    exact (ChartPullbacks.stableHilbertChartToRank R i j D P).w)

theorem stableHilbertChartOver_rankParameter (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    stableHilbertChartOver R i D P hP hD j ≫ stableHilbertRankParameterOver R i D P hP hD =
      ChartPullbacks.stableHilbertChartToRank R i j D P :=
  Over.OverMorphism.ext (stableHilbertChart_rankParameter R i D P hP hD j)

theorem stableHilbertCharts_cover (x : stableHilbertScheme R i D P hP hD) :
    ∃ j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m,
      ∃ y : (Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D P).left, stableHilbertChart R i D P hP hD j y = x :=
  by
    obtain ⟨j, y, hy⟩ := (stableHilbertGlueData R i D P hP hD).ι_jointly_surjective x
    exact ⟨j.down, y, hy⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.Scheme
