import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.RankChartPullbacks
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.MonoFamilyGluing

/-! # Polynomial Rank Scheme -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.PolynomialRankScheme

noncomputable section

/-! The polynomial rank charts glue along their actual intersections.
The resulting scheme maps monomorphically to the stable configuration
open and is covered by the original rank loci. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.MonoFamilyGluing
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {n m : ℕ} (i : Fin m) (D q : ℕ)

def stablePolynomialRankGlueData : Scheme.GlueData :=
  HilbertScheme.Presentations.Relative.MonoFamilyGluing.relativeMonoFamilyGlueData (BalancedProjectiveOpen.stableBalancedQuotientScheme R (r := n + 1) i)
    (fun j : ULift.{u} (BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) =>
      ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j.down D q)
    (fun j : ULift.{u} (BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) =>
      RankChartsOverBase.stableRankChartToStable R i j.down D q)

def stablePolynomialRankScheme : Scheme.{u} := (stablePolynomialRankGlueData R (n := n) i D q).glued

def stablePolynomialRankChart (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j D q).left ⟶
      stablePolynomialRankScheme R (n := n) i D q :=
  (stablePolynomialRankGlueData R i D q).ι (ULift.up j)

instance stablePolynomialRankChart_open (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    IsOpenImmersion (stablePolynomialRankChart R i D q j) :=
  Scheme.GlueData.ι_isOpenImmersion (stablePolynomialRankGlueData R i D q) (ULift.up j)

def stablePolynomialRankParameter : stablePolynomialRankScheme R (n := n) i D q ⟶
    (BalancedProjectiveOpen.stableBalancedQuotientScheme R (r := n + 1) i).left :=
  HilbertScheme.Presentations.Relative.MonoFamilyGluing.relativeMonoFamilyParameter (BalancedProjectiveOpen.stableBalancedQuotientScheme R (r := n + 1) i)
    (fun j : ULift.{u} (BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) =>
      ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j.down D q)
    (fun j : ULift.{u} (BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) =>
      RankChartsOverBase.stableRankChartToStable R i j.down D q)

theorem stablePolynomialRankChart_parameter (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    stablePolynomialRankChart R i D q j ≫ stablePolynomialRankParameter R i D q =
      (RankChartsOverBase.stableRankChartToStable R i j D q).left :=
  HilbertScheme.Presentations.Relative.MonoFamilyGluing.relativeMonoFamilyChart_parameter _ _ _ (ULift.up j)

instance stablePolynomialRankParameter_mono :
    Mono (stablePolynomialRankParameter R (n := n) i D q) :=
  HilbertScheme.Presentations.Relative.MonoFamilyGluing.relativeMonoFamilyParameter_mono _ _ _

instance stablePolynomialRankParameter_surjectiveOnStalks :
    SurjectiveOnStalks (stablePolynomialRankParameter R (n := n) i D q) :=
  HilbertScheme.Presentations.Relative.MonoFamilyGluing.relativeMonoFamilyParameter_surjectiveOnStalks _ _ _

instance stablePolynomialRankParameter_locallyOfFiniteType :
    LocallyOfFiniteType (stablePolynomialRankParameter R (n := n) i D q) := by
  have : IsZariskiLocalAtSource @LocallyOfFiniteType.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType.{u}) (Q := RingHom.FiniteType)
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType)
    (stablePolynomialRankGlueData R (n := n) i D q).openCover).mpr
  intro j
  change ULift.{u} (BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) at j
  change LocallyOfFiniteType (stablePolynomialRankChart R i D q j.down ≫ stablePolynomialRankParameter R i D q)
  rw [stablePolynomialRankChart_parameter]
  infer_instance

def stablePolynomialRankOver : Over (Spec (.of R)) :=
  Over.mk (stablePolynomialRankParameter R (n := n) i D q ≫ (BalancedProjectiveOpen.stableBalancedQuotientScheme R (r := n + 1) i).hom)

def stablePolynomialRankParameterOver : stablePolynomialRankOver R (n := n) i D q ⟶
    BalancedProjectiveOpen.stableBalancedQuotientScheme R (r := n + 1) i :=
  Over.homMk (stablePolynomialRankParameter R i D q) rfl

instance stablePolynomialRankParameterOver_mono :
    Mono (stablePolynomialRankParameterOver R (n := n) i D q) :=
  by
    have : Mono (stablePolynomialRankParameterOver R (n := n) i D q).left :=
      inferInstanceAs (Mono (stablePolynomialRankParameter R (n := n) i D q))
    exact Over.mono_of_mono_left _

def stablePolynomialRankChartOver (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j D q ⟶ stablePolynomialRankOver R (n := n) i D q :=
  Over.homMk (stablePolynomialRankChart R i D q j) (by
    change stablePolynomialRankChart R i D q j ≫
      (stablePolynomialRankParameter R i D q ≫ (BalancedProjectiveOpen.stableBalancedQuotientScheme R (r := n + 1) i).hom) = _
    rw [← Category.assoc, stablePolynomialRankChart_parameter]
    exact (RankChartsOverBase.stableRankChartToStable R i j D q).w)

theorem stablePolynomialRankChartOver_parameter (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m) :
    stablePolynomialRankChartOver R i D q j ≫ stablePolynomialRankParameterOver R i D q =
      RankChartsOverBase.stableRankChartToStable R i j D q :=
  Over.OverMorphism.ext (stablePolynomialRankChart_parameter R i D q j)

theorem stablePolynomialRankCharts_cover (x : stablePolynomialRankScheme R (n := n) i D q) :
    ∃ j : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m,
      ∃ y : (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j D q).left,
        stablePolynomialRankChart R i D q j y = x :=
  by
    obtain ⟨j, y, hy⟩ := (stablePolynomialRankGlueData R i D q).ι_jointly_surjective x
    exact ⟨j.down, y, hy⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.PolynomialRankScheme
