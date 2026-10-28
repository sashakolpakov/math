import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonomorphicOpenChartsExistential
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerOverlap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiFiniteQuasiProjectivity

/-! # Graph Power Gluing -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerGluing.StableHilbertGraphPowerGluing

noncomputable section

/-! The presented stable graph-power charts glue to an actual
quasi-projective scheme. The overlaps are their fiber products over the
original stable Hilbert scheme; saturation follows from the constructed
full-level comparisons and the exact graph-power lifting criterion. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (R : Type) [CommRing R] [IsNoetherianRing R] {n m : ℕ}
    (i : Fin m) (D : ℕ) (H : Polynomial ℚ)
    (hH : HilbertScheme.Presentations.BoundedHilbert.DegreeLocus.GradedHilbert.RankProfileRealizes.{0} n D (HilbertScheme.Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{0} n D H) H)
    (hD : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{0} n H ≤ D)
    (g : ℕ) (Hm Hi : Polynomial ℚ) (N : ℕ) [NeZero N]
    (labels : Fin m ≃ Multiplicative (Fin (2 * g) → ZMod N))
    (d : ℕ) (δ : Fin g → ℕ) (Φ : GraphPower.LocusPresentation.GraphPowerLocusFactory R g N d δ)

/-- The original Hilbert charts and the supplied graph-power loci
provide every chart and overlap map of the gluing. -/
def chartData : MonomorphicOpenTo.MonomorphicOpenCharts (StableHilbert.Scheme.stableHilbertOver R i D H hH hD)
    (Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :=
  MonomorphicOpenTo.MonomorphicOpenCharts.ofOverlapExists
    (fun j => Stable.ConfigurationLocus.stableConfigurationHilbertLocus R i j D H)
    (fun j => StableHilbert.Scheme.stableHilbertChartOver R i D H hH hD j)
    (fun j => StableHilbert.Scheme.stableHilbertChart_open R i D H hH hD j)
    (StableHilbert.Scheme.stableHilbertCharts_cover R i D H hH hD)
    (fun j => GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ)
    (fun j => GraphPowerChartMaps.StableHilbertGraphPower.toHilbertChart R i j D H hH g Hm Hi N labels d δ Φ)
    (fun _ => inferInstance)
    (fun j k => GraphPowerOverlap.StableHilbertGraphPowerOverlap.exists_ambientLift
      R i D H hH hD g Hm Hi N labels d δ Φ j k)

def overlap (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) : Over (Spec (.of R)) :=
  pullback ((chartData R i D H hH hD g Hm Hi N labels d δ Φ).toAmbient j)
    ((chartData R i D H hH hD g Hm Hi N labels d δ Φ).toAmbient k)

def overlapLeft (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    overlap R i D H hH hD g Hm Hi N labels d δ Φ j k ⟶
      GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ :=
  pullback.fst _ _

def overlapRight (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    overlap R i D H hH hD g Hm Hi N labels d δ Φ j k ⟶
      GraphPowerParameter.StableHilbertGraphPower.parameter R i k D H hH g Hm Hi N labels d δ Φ :=
  pullback.snd _ _

instance overlapLeft_open (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    IsOpenImmersion (overlapLeft R i D H hH hD g Hm Hi N labels d δ Φ j k).left :=
  (chartData R i D H hH hD g Hm Hi N labels d δ Φ).intersection_open j k

instance overlapRight_open (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    IsOpenImmersion (overlapRight R i D H hH hD g Hm Hi N labels d δ Φ j k).left :=
  (chartData R i D H hH hD g Hm Hi N labels d δ Φ).intersection_snd_open j k

/-- Pairwise overlaps are actual ambient fiber products, with the
canonical symmetry and triple-overlap maps of mono-family gluing. -/
def glueData : Scheme.GlueData :=
  (chartData R i D H hH hD g Hm Hi N labels d δ Φ).glueData

def parameter : Over (Spec (.of R)) :=
  (chartData R i D H hH hD g Hm Hi N labels d δ Φ).over

theorem parameter_left :
    (parameter R i D H hH hD g Hm Hi N labels d δ Φ).left =
      (StableHilbertGraphPowerGluing.glueData R i D H hH hD g Hm Hi N labels d δ Φ).glued := rfl

def inclusion : parameter R i D H hH hD g Hm Hi N labels d δ Φ ⟶
    StableHilbert.Scheme.stableHilbertOver R i D H hH hD :=
  (chartData R i D H hH hD g Hm Hi N labels d δ Φ).inclusion

def chartMap (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ ⟶
      parameter R i D H hH hD g Hm Hi N labels d δ Φ :=
  (chartData R i D H hH hD g Hm Hi N labels d δ Φ).chartOver j

instance chartMap_open (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    IsOpenImmersion (StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ j).left :=
  (chartData R i D H hH hD g Hm Hi N labels d δ Φ).chartInclusion_open j

theorem chartMap_inclusion (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ j ≫
        StableHilbertGraphPowerGluing.inclusion R i D H hH hD g Hm Hi N labels d δ Φ =
      GraphPowerChartMaps.StableHilbertGraphPower.toHilbertChart R i j D H hH g Hm Hi N labels d δ Φ ≫
        StableHilbert.Scheme.stableHilbertChartOver R i D H hH hD j :=
  (chartData R i D H hH hD g Hm Hi N labels d δ Φ).chartOver_inclusion j

theorem charts_cover (x : (parameter R i D H hH hD g Hm Hi N labels d δ Φ).left) :
    ∃ j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m,
      ∃ y : (GraphPowerParameter.StableHilbertGraphPower.parameter R i j D H hH g Hm Hi N labels d δ Φ).left,
        (StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ j).left y = x :=
  (chartData R i D H hH hD g Hm Hi N labels d δ Φ).charts_cover x

theorem chart_intersection (j k : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    IsPullback (overlapLeft R i D H hH hD g Hm Hi N labels d δ Φ j k).left
      (overlapRight R i D H hH hD g Hm Hi N labels d δ Φ j k).left
      (StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ j).left
      (StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ k).left :=
  (chartData R i D H hH hD g Hm Hi N labels d δ Φ).chart_intersection j k

/-- Base change along an original stable Hilbert open gives exactly
the original normalized polarization chart, with its full scheme structure. -/
theorem chart_isPullback (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    IsPullback (StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ j).left
      (GraphPowerChartMaps.StableHilbertGraphPower.toHilbertChart R i j D H hH g Hm Hi N labels d δ Φ).left
      (StableHilbertGraphPowerGluing.inclusion R i D H hH hD g Hm Hi N labels d δ Φ).left
      (StableHilbert.Scheme.stableHilbertChart R i D H hH hD j) :=
  (chartData R i D H hH hD g Hm Hi N labels d δ Φ).chart_isPullback j

theorem chartOver_isPullback (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{0} (n + 1) m) :
    IsPullback (StableHilbertGraphPowerGluing.chartMap R i D H hH hD g Hm Hi N labels d δ Φ j)
      (GraphPowerChartMaps.StableHilbertGraphPower.toHilbertChart R i j D H hH g Hm Hi N labels d δ Φ)
      (StableHilbertGraphPowerGluing.inclusion R i D H hH hD g Hm Hi N labels d δ Φ)
      (StableHilbert.Scheme.stableHilbertChartOver R i D H hH hD j) :=
  (chartData R i D H hH hD g Hm Hi N labels d δ Φ).chartOver_isPullback j

instance inclusion_mono : Mono (StableHilbertGraphPowerGluing.inclusion R i D H hH hD g Hm Hi N labels d δ Φ) :=
  (chartData R i D H hH hD g Hm Hi N labels d δ Φ).inclusion_mono

instance inclusion_left_mono : Mono (StableHilbertGraphPowerGluing.inclusion R i D H hH hD g Hm Hi N labels d δ Φ).left :=
  (chartData R i D H hH hD g Hm Hi N labels d δ Φ).inclusion_left_mono

instance inclusion_locallyOfFiniteType :
    LocallyOfFiniteType (StableHilbertGraphPowerGluing.inclusion R i D H hH hD g Hm Hi N labels d δ Φ).left := by
  let C := chartData R i D H hH hD g Hm Hi N labels d δ Φ
  let : ∀ j, LocallyOfFiniteType (C.chartMap j).left := fun j =>
    GraphPowerChartMaps.StableHilbertGraphPower.toHilbertChart_locallyOfFiniteType R i j D H hH g Hm Hi N labels d δ Φ
  exact C.inclusion_locallyOfFiniteType

instance inclusion_quasiCompact :
    QuasiCompact (StableHilbertGraphPowerGluing.inclusion R i D H hH hD g Hm Hi N labels d δ Φ).left := by
  let C := chartData R i D H hH hD g Hm Hi N labels d δ Φ
  let : ∀ j, QuasiCompact (C.chartMap j).left := fun j =>
    GraphPowerChartMaps.StableHilbertGraphPower.toHilbertChart_quasiCompact R i j D H hH g Hm Hi N labels d δ Φ
  exact C.inclusion_quasiCompact

/-- The quasi-projective presentation is obtained from the genuine
finite-type monomorphism into the original stable Hilbert parameter. -/
def quasiProjective :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (parameter R i D H hH hD g Hm Hi N labels d δ Φ) :=
  (QuasiProjectivity.stableHilbertOver_quasiProjective R i D H hH hD).some.monomorphismSource
    (StableHilbertGraphPowerGluing.inclusion R i D H hH hD g Hm Hi N labels d δ Φ)

instance parameter_noetherian :
    IsNoetherian (parameter R i D H hH hD g Hm Hi N labels d δ Φ).left :=
  (quasiProjective R i D H hH hD g Hm Hi N labels d δ Φ).noetherian

/-- The same scheme retains its actual monomorphic map into the
original stable balanced configuration quotient. -/
def toBalanced : parameter R i D H hH hD g Hm Hi N labels d δ Φ ⟶
    Stable.BalancedProjectiveOpen.stableBalancedQuotientScheme R (r := n + 1) i :=
  StableHilbertGraphPowerGluing.inclusion R i D H hH hD g Hm Hi N labels d δ Φ ≫
    StableHilbert.Scheme.stableHilbertRankParameterOver R i D H hH hD ≫
      Stable.PolynomialRankScheme.stablePolynomialRankParameterOver R i D (Stable.ConfigurationLocus.configurationHilbertRank D H)

instance toBalanced_mono : Mono (toBalanced R i D H hH hD g Hm Hi N labels d δ Φ) := by
  dsimp only [toBalanced]
  infer_instance

instance toBalanced_left_mono : Mono (toBalanced R i D H hH hD g Hm Hi N labels d δ Φ).left :=
  Over.mono_left_of_mono _

instance toBalanced_locallyOfFiniteType :
    LocallyOfFiniteType (toBalanced R i D H hH hD g Hm Hi N labels d δ Φ).left := by
  dsimp only [toBalanced, Over.comp_left]
  infer_instance

instance toBalanced_quasiCompact :
    QuasiCompact (toBalanced R i D H hH hD g Hm Hi N labels d δ Φ).left := by
  dsimp only [toBalanced, Over.comp_left]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.GraphPowerGluing.StableHilbertGraphPowerGluing
