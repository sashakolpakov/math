import OAI.RepresentationTheory.Theta.Geometric.Universal.BallInjectivity
import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.DimensionBound

/-! # Dimension Bound -/

namespace OAI.RepresentationTheory.Theta.Geometric.Universal.DimensionBound

noncomputable section

/-! Every actual smooth integral moduli subspace has dimension at most
two, using the constructed injective local ball periods. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (f : S ⟶ D.complexSpace) [Mono f] (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)

include hg f x in
theorem complexUniversal_dimension_le_two (hs : 0 < s)
    (hdegree : Module.finrank ℚ E = 2 * s) : AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension S.hom ≤ 2 := by
  obtain ⟨O, period, hO, hxO, hhol, _, hi⟩ :=
    BallInjectivity.exists_complexUniversal_injective_ball_periods D hg f x hs hdegree
  have hdim := Holomorphic.DimensionBound.finrank_le_of_holomorphic_injOn hO ⟨_, hxO⟩ hhol hi
  rw [FamilyPeriodCharts.complexUniversalFamilyCharts_dimension D f x] at hdim
  simpa only [Geometry.ComplexBall.PrescribedSignsB.BallChart, Module.finrank_pi, Module.finrank_self, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using hdim

end

end OAI.RepresentationTheory.Theta.Geometric.Universal.DimensionBound
