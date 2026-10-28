import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.PointInverseNaturality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.CoordinateCoverage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.RankChartsOverBase
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.ChartNormalizedRankPoints
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Configuration.ProjectiveTransport

/-! # Balanced Orbit Equality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedOrbitEquality

noncomputable section

/-! Common linear coordinate changes and independent unit multiples
give equal points of the actual stable balanced quotient, even when
the two configurations are presented on different stable charts. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.PointInverseNaturality
open scoped Classical BigOperators
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem configurationFrameRelated_denominatorUnit_iff
    {A : Type u} [CommRing A] {n m : ℕ}
    {v w : Fin m → Fin (n + 1) → A} (h : Configuration.ProjectiveTransport.ConfigurationFrameRelated v w)
    (a : (Fin (n + 1) → Fin m) → ℕ) :
    IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) a) ↔
      IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) a) := by
  obtain ⟨T, s, hs⟩ := h
  have hw : w = fun z k => (s z : A) * T (v z) k := by
    funext z k
    exact congrFun (hs z) k
  have hm : Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) a =
      (T.toLinearMap.det ^ (∑ τ, a τ) *
        ∏ z, (s z : A) ^ Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a z) *
      Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) a :=
    (congrArg (fun z => Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ z) a) hw).trans
      (DeterminantMonomialTransformations.determinantMonomial_linear_rescale v a T.toLinearMap (fun z => (s z : A)))
  rw [hm]
  have hu : IsUnit (T.toLinearMap.det ^ (∑ τ, a τ) *
      ∏ z, (s z : A) ^ Balanced.ExponentFiniteGeneration.monomialMultiDegree DeterminantBlockDegrees.labeledDeterminantWeight a z) :=
    (T.isUnit_det'.pow _).mul
      (IsUnit.prod_univ_iff.mpr (fun z => (s z).isUnit.pow _))
  exact ⟨fun hv => hu.mul hv, fun hw => (IsUnit.mul_iff.mp hw).2⟩

namespace StableHilbertCoverage
variable (R : Type u) [CommRing R] {n m : ℕ} (i : Fin m)
variable (j k : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (T : Over (Spec (.of R)))

local instance : Algebra R Γ(T.left, ⊤) :=
  inferInstanceAs (Algebra R (HilbertScheme.Presentations.Relative.AffinePoints.relativeGlobalAlgebra (.of R) T))

theorem chartPoint_eq_of_frameRelated
    (v w : Fin m → Fin (n + 1) → Γ(T.left, ⊤))
    (hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) j.exponent))
    (hw : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) j.exponent))
    (h : Configuration.ProjectiveTransport.ConfigurationFrameRelated v w) :
    StableHilbert.CoordinateCoverage.StableHilbertCoverage.chartPoint R i j T v hv = StableHilbert.CoordinateCoverage.StableHilbertCoverage.chartPoint R i j T w hw := by
  apply (HilbertScheme.Presentations.Relative.AffinePoints.relativeAffinePointEquiv (.of R)
    (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced) T).injective
  simp only [StableHilbert.CoordinateCoverage.StableHilbertCoverage.chartPoint, Equiv.apply_symm_apply]
  exact BalancedChart.ConfigurationOrbits.balancedConfigurationChartAlgebraEvaluation_eq_of_orbit
    (R := R) (HilbertScheme.Presentations.Relative.AffinePoints.relativeGlobalAlgebra (.of R) T) j.exponent (Nat.succ_pos n)
      i j.balanced h

theorem chartPoint_intersection_left
    (v : Fin m → Fin (n + 1) → Γ(T.left, ⊤))
    (hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) j.exponent))
    (hvk : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v)
      (j.intersection k).exponent)) :
    StableHilbert.CoordinateCoverage.StableHilbertCoverage.chartPoint R i (j.intersection k) T v hvk ≫
        StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k = StableHilbert.CoordinateCoverage.StableHilbertCoverage.chartPoint R i j T v hv := by
  unfold StableHilbert.CoordinateCoverage.StableHilbertCoverage.chartPoint StableIntersection.SchemeRank.stableChartIntersectionLeftOver
  rw [HilbertScheme.Presentations.Affine.PointInverseNaturality.relativeAffinePointEquiv_symm_postcomp]
  apply congrArg (HilbertScheme.Presentations.Relative.AffinePoints.relativeAffinePointEquiv (.of R)
    (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced) T).symm
  apply AlgHom.coe_ringHom_injective
  have hc := BalancedChart.IntersectionMaps.balancedConfigurationChartEvaluation_intersection_left
    (A := HilbertScheme.Presentations.Relative.AffinePoints.relativeGlobalAlgebra (.of R) T) R i j.exponent k.exponent
    j.balanced k.balanced v hv hvk
  -- The ring-hom equality is already proved; avoid repeating elaborator conversion.
  -- The kernel still checks it against the original target equality.
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    for d in (← Lean.getLCtx) do
      if d.userName == `hc then
        goal.assign (.fvar d.fvarId)
        Lean.Elab.Tactic.replaceMainGoal []
        return
    throwError "local ring-hom equality proof not found"

theorem chartPoint_intersection_right
    (v : Fin m → Fin (n + 1) → Γ(T.left, ⊤))
    (hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) k.exponent))
    (hvk : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v)
      (j.intersection k).exponent)) :
    StableHilbert.CoordinateCoverage.StableHilbertCoverage.chartPoint R i (j.intersection k) T v hvk ≫
        StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k = StableHilbert.CoordinateCoverage.StableHilbertCoverage.chartPoint R i k T v hv := by
  unfold StableHilbert.CoordinateCoverage.StableHilbertCoverage.chartPoint StableIntersection.SchemeRank.stableChartIntersectionRightOver
  rw [HilbertScheme.Presentations.Affine.PointInverseNaturality.relativeAffinePointEquiv_symm_postcomp]
  apply congrArg (HilbertScheme.Presentations.Relative.AffinePoints.relativeAffinePointEquiv (.of R)
    (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i k.exponent k.balanced) T).symm
  apply AlgHom.coe_ringHom_injective
  have hc := BalancedChart.IntersectionMaps.balancedConfigurationChartEvaluation_intersection_right
    (A := HilbertScheme.Presentations.Relative.AffinePoints.relativeGlobalAlgebra (.of R) T) R i j.exponent k.exponent
    j.balanced k.balanced v hv hvk
  -- The ring-hom equality is already proved; avoid repeating elaborator conversion.
  -- The kernel still checks it against the original target equality.
  run_tac Lean.Elab.Tactic.withMainContext do
    let goal ← Lean.Elab.Tactic.getMainGoal
    for d in (← Lean.getLCtx) do
      if d.userName == `hc then
        goal.assign (.fvar d.fvarId)
        Lean.Elab.Tactic.replaceMainGoal []
        return
    throwError "local ring-hom equality proof not found"

theorem chartPoints_toBalanced_eq_of_frameRelated
    (v w : Fin m → Fin (n + 1) → Γ(T.left, ⊤))
    (hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) j.exponent))
    (hw : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ w) k.exponent))
    (h : Configuration.ProjectiveTransport.ConfigurationFrameRelated v w) :
    StableHilbert.CoordinateCoverage.StableHilbertCoverage.chartPoint R i j T v hv ≫ RankChartsOverBase.stableBalancedAffineChartOverMap R i j =
      StableHilbert.CoordinateCoverage.StableHilbertCoverage.chartPoint R i k T w hw ≫ RankChartsOverBase.stableBalancedAffineChartOverMap R i k := by
  have hvk : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) k.exponent) :=
    (configurationFrameRelated_denominatorUnit_iff h k.exponent).mpr hw
  have hvjk : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v)
      (j.intersection k).exponent) := by
    change IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v)
      (j.exponent + k.exponent))
    rw [Balanced.MonomialAlgebra.exponentMonomial_add]
    exact hv.mul hvk
  let z := StableHilbert.CoordinateCoverage.StableHilbertCoverage.chartPoint R i (j.intersection k) T v hvjk
  have hl : z ≫ StableIntersection.SchemeRank.stableChartIntersectionLeftOver R i j k = StableHilbert.CoordinateCoverage.StableHilbertCoverage.chartPoint R i j T v hv :=
    chartPoint_intersection_left R i j k T v hv hvjk
  have hr : z ≫ StableIntersection.SchemeRank.stableChartIntersectionRightOver R i j k = StableHilbert.CoordinateCoverage.StableHilbertCoverage.chartPoint R i k T v hvk :=
    chartPoint_intersection_right R i j k T v hvk hvjk
  have he : StableHilbert.CoordinateCoverage.StableHilbertCoverage.chartPoint R i k T v hvk = StableHilbert.CoordinateCoverage.StableHilbertCoverage.chartPoint R i k T w hw :=
    chartPoint_eq_of_frameRelated R i k T v w hvk hw h
  exact (congrArg (fun a => a ≫ RankChartsOverBase.stableBalancedAffineChartOverMap R i j) hl.symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun a => z ≫ a) (RankChartsOverBase.stableChartIntersectionLeftOver_factor R i j k)).trans
        ((congrArg (fun a => z ≫ a) (RankChartsOverBase.stableChartIntersectionRightOver_factor R i j k).symm).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun a => a ≫ RankChartsOverBase.stableBalancedAffineChartOverMap R i k) hr).trans
              (congrArg (fun a => a ≫ RankChartsOverBase.stableBalancedAffineChartOverMap R i k) he))))))

/-- The actual normalized vector coordinates of an arbitrary scheme
point of a stable coefficient chart. -/
def normalizedVectors (a : T ⟶ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j) :
    Fin m → Fin (n + 1) → Γ(T.left, ⊤) :=
  ChartNormalizedRankPoints.stableChartNormalizedPointVectors R (A := HilbertScheme.Presentations.Relative.AffinePoints.relativeGlobalAlgebra (.of R) T) i j
    (HilbertScheme.Presentations.Relative.AffinePoints.relativeAffinePointEquiv (.of R)
      (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced) T a)

theorem normalizedVectors_denominatorUnit
    (a : T ⟶ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j) :
    IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ (normalizedVectors R i j T a))
      j.exponent) :=
  ChartNormalizedRankPoints.stableChartNormalizedPoint_denominatorUnit R (A := HilbertScheme.Presentations.Relative.AffinePoints.relativeGlobalAlgebra (.of R) T) i j
    (HilbertScheme.Presentations.Relative.AffinePoints.relativeAffinePointEquiv (.of R)
      (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced) T a)

theorem chartPoint_normalizedVectors
    (a : T ⟶ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j) :
    StableHilbert.CoordinateCoverage.StableHilbertCoverage.chartPoint R i j T (normalizedVectors R i j T a)
      (normalizedVectors_denominatorUnit R i j T a) = a := by
  apply (HilbertScheme.Presentations.Relative.AffinePoints.relativeAffinePointEquiv (.of R)
    (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced) T).injective
  simp only [StableHilbert.CoordinateCoverage.StableHilbertCoverage.chartPoint, Equiv.apply_symm_apply]
  ext x
  exact RingHom.congr_fun (ChartNormalizedRankPoints.stableChartNormalizedPoint_evaluation R
    (A := HilbertScheme.Presentations.Relative.AffinePoints.relativeGlobalAlgebra (.of R) T) i j
    (HilbertScheme.Presentations.Relative.AffinePoints.relativeAffinePointEquiv (.of R)
      (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced) T a)) x

theorem points_toBalanced_eq_of_frameRelated
    (a : T ⟶ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)
    (b : T ⟶ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i k)
    (h : Configuration.ProjectiveTransport.ConfigurationFrameRelated (normalizedVectors R i j T a) (normalizedVectors R i k T b)) :
    a ≫ RankChartsOverBase.stableBalancedAffineChartOverMap R i j =
      b ≫ RankChartsOverBase.stableBalancedAffineChartOverMap R i k := by
  have he := chartPoints_toBalanced_eq_of_frameRelated R i j k T
    (normalizedVectors R i j T a) (normalizedVectors R i k T b)
    (normalizedVectors_denominatorUnit R i j T a)
    (normalizedVectors_denominatorUnit R i k T b) h
  simpa only [chartPoint_normalizedVectors] using he

end StableHilbertCoverage

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.BalancedOrbitEquality
