import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.ConfigurationPolynomialRankLocus

/-! # Polynomial Matrix Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.PolynomialMatrixCoefficients

noncomputable section

/-! An affine point of the stable chart pulls the universal polynomial
matrix back to the literal monomial matrix of its evaluated normalized
configuration. All coefficient maps are the actual scheme maps. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical
universe u
variable (R : Type u) [CommRing R] {n m : ℕ}
variable (i : Fin m) (j : BalancedFrameIndex.StableBalancedFrameIndex.{u} (n + 1) m)
variable (A : CommRingCat.{u}) {f : Spec A ⟶ Spec (.of R)}
variable (x : Over.mk f ⟶ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)

def stablePolynomialChartPointCoefficients : Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced →+* A :=
  (Scheme.ΓSpecIso A).hom.hom.comp (x.left.appTop.hom.comp
    (Scheme.ΓSpecIso (.of (Balanced.FrameChartCoordinates.balancedDeterminantChartRing R i j.exponent j.balanced))).inv.hom)

def stablePolynomialChartPointVectors : ULift.{u} (Fin m) → Fin (n + 1) → A :=
  fun c k => stablePolynomialChartPointCoefficients R i j A x
    (Balanced.FrameChartNormalization.balancedFrameChartVectors R i j.frame j.additional j.coordinate j.exponent j.complement
      j.balanced j.complete c.down k)

theorem stablePolynomialChartPointVectors_selected (c : ULift.{u} (Fin m)) :
    stablePolynomialChartPointVectors R i j A x c (j.coordinate c.down) = 1 := by
  change stablePolynomialChartPointCoefficients R i j A x
    (Balanced.FrameChartNormalization.balancedFrameChartVectors R i j.frame j.additional j.coordinate j.exponent j.complement
      j.balanced j.complete c.down (j.coordinate c.down)) = 1
  rw [Balanced.FrameChartNormalization.balancedFrameChartVectors_selected, map_one]

theorem stableConfigurationPolynomialMatrix_coefficients (D : ℕ) :
    HilbertConstruction.Matrix.RankAffineCriterion.affineMatrixCoefficients (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankAmbient R i j)
      (ConfigurationPolynomialRankLocus.stableConfigurationPolynomialMatrix R i j D) A x =
      Configuration.MonomialMatrix.configurationMonomialMatrix (stablePolynomialChartPointVectors R i j A x) D := by
  have h := Configuration.MonomialMatrix.configurationMonomialMatrix_map (d := D) (stablePolynomialChartPointCoefficients R i j A x)
    (fun c : ULift.{u} (Fin m) => Balanced.FrameChartNormalization.balancedFrameChartVectors R i j.frame j.additional j.coordinate
      j.exponent j.complement j.balanced j.complete c.down)
  exact h

theorem stablePolynomialRankPoint_iff_configuration (D k : ℕ) :
    (∃! y : Over.mk f ⟶ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus R i j D k,
      y ≫ ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankInclusion R i j D k = x) ↔
    (Module.Flat A ((ULift.{u} (Fin m) → A) ⧸
      (Matrix.toLin' (Configuration.MonomialMatrix.configurationMonomialMatrix (stablePolynomialChartPointVectors R i j A x) D)).range) ∧
      ∀ p : PrimeSpectrum A, Module.rankAtStalk (R := A)
        ((ULift.{u} (Fin m) → A) ⧸
          (Matrix.toLin' (Configuration.MonomialMatrix.configurationMonomialMatrix (stablePolynomialChartPointVectors R i j A x) D)).range) p + k = m) := by
  rw [ConfigurationPolynomialRankLocus.stableConfigurationPolynomialRankLocus_affine_iff, stableConfigurationPolynomialMatrix_coefficients]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Stable.PolynomialMatrixCoefficients
