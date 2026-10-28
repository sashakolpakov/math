import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonomorphicOpenChartsExistential
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationOverlapExistence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiFiniteQuasiProjectivity

/-! # Polarization Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationGluing.StableHilbertPolarizationGluing

noncomputable section

/-! The stable normalized polarization charts glue to an actual
quasi-projective scheme. The overlaps are their fiber products over the
original stable Hilbert scheme; saturation follows from the constructed
full-level and normalized-polarization transitions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (qR : Spec (.of R) ⟶ Spec (.of ℚ))
    (d : ℕ) (hd : 0 < d) (δ : Fin g → ℕ) (hδ : ∀ k, 0 < δ k)

/-- Every field is supplied by the original charts and their proved
transition maps. No invariance or gluing premise is an input. -/
def chartData : MonomorphicOpenTo.MonomorphicOpenCharts (StableHilbert.Scheme.stableHilbertOver R i D H hH hD)
    (Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :=
  MonomorphicOpenTo.MonomorphicOpenCharts.ofOverlapExists
    (fun j => Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (fun j => StableHilbert.Scheme.stableHilbertChartOver R i D H hH hD j)
    (fun j => StableHilbert.Scheme.stableHilbertChart_open R i D H hH hD j)
    (StableHilbert.Scheme.stableHilbertCharts_cover R i D H hH hD)
    (fun j => PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ)
    (fun j => PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ)
    (fun _ => inferInstance)
    (fun j k => PolarizationOverlapExistence.StableHilbertPolarizationOverlap.exists_ambientLift
      R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k)

def overlap (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) : Over (Spec (.of R)) :=
  pullback ((chartData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).toAmbient j)
    ((chartData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).toAmbient k)

def overlapLeft (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    overlap R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k ⟶
      PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ :=
  pullback.fst _ _

def overlapRight (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    overlap R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k ⟶
      PolarizationParameter.StableHilbertPolarization.parameter R i k D H hH g Hm Hi N labels qR d hd δ hδ :=
  pullback.snd _ _

instance overlapLeft_open (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    IsOpenImmersion (overlapLeft R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).left :=
  (chartData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).intersection_open j k

instance overlapRight_open (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    IsOpenImmersion (overlapRight R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).left :=
  (chartData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).intersection_snd_open j k

/-- Pairwise overlaps are actual ambient fiber products, with the
canonical symmetry and triple-overlap maps of mono-family gluing. -/
def glueData : Scheme.GlueData :=
  (chartData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).glueData

def parameter : Over (Spec (.of R)) :=
  (chartData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).over

theorem parameter_left :
    (parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ).left =
      (StableHilbertPolarizationGluing.glueData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).glued := rfl

def inclusion : parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ ⟶
    StableHilbert.Scheme.stableHilbertOver R i D H hH hD :=
  (chartData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).inclusion

def chartMap (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ ⟶
      parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ :=
  (chartData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).chartOver j

instance chartMap_open (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    IsOpenImmersion (StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ j).left :=
  (chartData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).chartInclusion_open j

theorem chartMap_inclusion (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ j ≫
        StableHilbertPolarizationGluing.inclusion R i D H hH hD g Hm Hi N labels qR d hd δ hδ =
      PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ ≫
        StableHilbert.Scheme.stableHilbertChartOver R i D H hH hD j :=
  (chartData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).chartOver_inclusion j

theorem charts_cover (x : (parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ).left) :
    ∃ j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m,
      ∃ y : (PolarizationParameter.StableHilbertPolarization.parameter R i j D H hH g Hm Hi N labels qR d hd δ hδ).left,
        (StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ j).left y = x :=
  (chartData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).charts_cover x

theorem chart_intersection (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    IsPullback (overlapLeft R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).left
      (overlapRight R i D H hH hD g Hm Hi N labels qR d hd δ hδ j k).left
      (StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ j).left
      (StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ k).left :=
  (chartData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).chart_intersection j k

/-- Base change along an original stable Hilbert open gives exactly
the original normalized polarization chart, with its full scheme structure. -/
theorem chart_isPullback (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    IsPullback (StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ j).left
      (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ).left
      (StableHilbertPolarizationGluing.inclusion R i D H hH hD g Hm Hi N labels qR d hd δ hδ).left
      (StableHilbert.Scheme.stableHilbertChart R i D H hH hD j) :=
  (chartData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).chart_isPullback j

theorem chartOver_isPullback (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    IsPullback (StableHilbertPolarizationGluing.chartMap R i D H hH hD g Hm Hi N labels qR d hd δ hδ j)
      (PolarizationChartMaps.StableHilbertPolarization.toHilbertChart R i j D H hH g Hm Hi N labels qR d hd δ hδ)
      (StableHilbertPolarizationGluing.inclusion R i D H hH hD g Hm Hi N labels qR d hd δ hδ)
      (StableHilbert.Scheme.stableHilbertChartOver R i D H hH hD j) :=
  (chartData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).chartOver_isPullback j

instance inclusion_mono : Mono (StableHilbertPolarizationGluing.inclusion R i D H hH hD g Hm Hi N labels qR d hd δ hδ) :=
  (chartData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).inclusion_mono

instance inclusion_left_mono : Mono (StableHilbertPolarizationGluing.inclusion R i D H hH hD g Hm Hi N labels qR d hd δ hδ).left :=
  (chartData R i D H hH hD g Hm Hi N labels qR d hd δ hδ).inclusion_left_mono

instance inclusion_locallyOfFiniteType :
    LocallyOfFiniteType (StableHilbertPolarizationGluing.inclusion R i D H hH hD g Hm Hi N labels qR d hd δ hδ).left := by
  let C := chartData R i D H hH hD g Hm Hi N labels qR d hd δ hδ
  let : ∀ j, LocallyOfFiniteType (C.chartMap j).left := fun j =>
    PolarizationChartMaps.StableHilbertPolarization.toHilbertChart_locallyOfFiniteType R i j D H hH g Hm Hi N labels qR d hd δ hδ
  exact C.inclusion_locallyOfFiniteType

instance inclusion_quasiCompact :
    QuasiCompact (StableHilbertPolarizationGluing.inclusion R i D H hH hD g Hm Hi N labels qR d hd δ hδ).left := by
  let C := chartData R i D H hH hD g Hm Hi N labels qR d hd δ hδ
  let : ∀ j, QuasiCompact (C.chartMap j).left := fun j =>
    PolarizationChartMaps.StableHilbertPolarization.toHilbertChart_quasiCompact R i j D H hH g Hm Hi N labels qR d hd δ hδ
  exact C.inclusion_quasiCompact

/-- The quasi-projective presentation is obtained from the genuine
finite-type monomorphism into the original stable Hilbert parameter. -/
def quasiProjective :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ) :=
  (QuasiProjectivity.stableHilbertOver_quasiProjective R i D H hH hD).some.monomorphismSource
    (StableHilbertPolarizationGluing.inclusion R i D H hH hD g Hm Hi N labels qR d hd δ hδ)

instance parameter_noetherian :
    IsNoetherian (parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ).left :=
  (quasiProjective R i D H hH hD g Hm Hi N labels qR d hd δ hδ).noetherian

/-- The same scheme retains its actual monomorphic map into the
original stable balanced configuration quotient. -/
def toBalanced : parameter R i D H hH hD g Hm Hi N labels qR d hd δ hδ ⟶
    Stable.BalancedProjectiveOpen.stableBalancedQuotientScheme R (r := n + 1) i :=
  StableHilbertPolarizationGluing.inclusion R i D H hH hD g Hm Hi N labels qR d hd δ hδ ≫
    StableHilbert.Scheme.stableHilbertRankParameterOver R i D H hH hD ≫
      Stable.PolynomialRankScheme.stablePolynomialRankParameterOver R i D (Stable.ConfigurationLocus.configurationHilbertRank D H)

instance toBalanced_mono : Mono (toBalanced R i D H hH hD g Hm Hi N labels qR d hd δ hδ) := by
  dsimp only [toBalanced]
  infer_instance

instance toBalanced_left_mono : Mono (toBalanced R i D H hH hD g Hm Hi N labels qR d hd δ hδ).left :=
  Over.mono_left_of_mono _

instance toBalanced_locallyOfFiniteType :
    LocallyOfFiniteType (toBalanced R i D H hH hD g Hm Hi N labels qR d hd δ hδ).left := by
  dsimp only [toBalanced, Over.comp_left]
  infer_instance

instance toBalanced_quasiCompact :
    QuasiCompact (toBalanced R i D H hH hD g Hm Hi N labels qR d hd δ hδ).left := by
  dsimp only [toBalanced, Over.comp_left]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.PolarizationGluing.StableHilbertPolarizationGluing
