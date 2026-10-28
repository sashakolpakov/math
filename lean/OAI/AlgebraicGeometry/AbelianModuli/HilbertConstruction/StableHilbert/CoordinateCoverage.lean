import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.PolynomialMatrixCoefficients
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.ConfigurationOrbits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.BalancedChart.OrbitNormalization
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffinePoints

/-! # Coordinate Coverage -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.CoordinateCoverage.StableHilbertCoverage

noncomputable section

/-! An actual vector configuration with invertible stable denominator
defines a point of the existing stable coefficient chart. Its universal
coordinates are the normalized original vectors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.AffinePoints
universe u
variable (R : Type u) [CommRing R] {n m : ℕ}
variable (i : Fin m) (j : Stable.BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (T : Over (Spec (.of R))) (v : Fin m → Fin (n + 1) → Γ(T.left, ⊤))
variable (hv : IsUnit (Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) j.exponent))

local instance : Algebra R Γ(T.left, ⊤) :=
  inferInstanceAs (Algebra R (HilbertScheme.Presentations.Relative.AffinePoints.relativeGlobalAlgebra (.of R) T))

def chartPoint : T ⟶ Stable.ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j :=
  (HilbertScheme.Presentations.Relative.AffinePoints.relativeAffinePointEquiv (.of R)
    (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced) T).symm
      (BalancedChart.ConfigurationOrbits.balancedConfigurationChartAlgebraEvaluation (R := R)
        (HilbertScheme.Presentations.Relative.AffinePoints.relativeGlobalAlgebra (.of R) T) j.exponent i j.balanced ⟨v, hv⟩)

theorem chartPoint_value (a : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced) :
    (chartPoint R i j T v hv).left.appTop
      ((Scheme.ΓSpecIso (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced))).inv a) =
        Balanced.ConfigurationChartEvaluation.balancedConfigurationChartEvaluation (R := R) i v j.exponent j.balanced hv a := by
  have h := congrArg (fun f => f a)
    ((HilbertScheme.Presentations.Relative.AffinePoints.relativeAffinePointEquiv (.of R)
      (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced) T).apply_symm_apply
        (BalancedChart.ConfigurationOrbits.balancedConfigurationChartAlgebraEvaluation (R := R)
          (HilbertScheme.Presentations.Relative.AffinePoints.relativeGlobalAlgebra (.of R) T) j.exponent i j.balanced ⟨v, hv⟩))
  exact h

theorem chartPoint_normalization :
    ∃ U : (Fin (n + 1) → Γ(T.left, ⊤)) ≃ₗ[Γ(T.left, ⊤)]
        (Fin (n + 1) → Γ(T.left, ⊤)),
      ∃ c : Fin m → Γ(T.left, ⊤)ˣ, ∀ z k,
        (chartPoint R i j T v hv).left.appTop
          ((Scheme.ΓSpecIso (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced))).inv
            (Balanced.FrameChartNormalization.balancedFrameChartVectors R i j.frame j.additional j.coordinate
              j.exponent j.complement j.balanced j.complete z k)) =
          (c z : Γ(T.left, ⊤)) * U (v z) k := by
  obtain ⟨U, c, hc⟩ := BalancedChart.OrbitNormalization.balancedChartEvaluation_is_frame_normalization
    (R := R) i j.frame j.additional j.coordinate j.exponent j.complement
      j.balanced j.complete
      ((Frame.ChartDenominators.frameDiscriminantExponent_le_chart j.frame j.additional j.coordinate).trans j.frame_le) v hv
  refine ⟨U, c, fun z k => ?_⟩
  rw [chartPoint_value]
  exact hc z k

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StableHilbert.CoordinateCoverage.StableHilbertCoverage
