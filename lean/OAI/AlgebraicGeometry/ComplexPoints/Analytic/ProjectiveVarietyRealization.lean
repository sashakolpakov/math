import OAI.AlgebraicGeometry.Foundations.Scheme.ComplexPointExistence
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveVarietyCompactness
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Projective Variety Realization -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# The analytic realization of an integral smooth projective variety

The space in this file is the actual relative scheme-point type, with the
analytic topology recovered on affine charts. Its manifold structure is the
proved regular-coordinate atlas, and its dimension is derived from the
function field. No topological or differential-geometric data are added to
the algebraic variety as assumptions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped ContDiff _root_.Manifold

/-- The genuine complex-valued points, with their ordinary analytic topology. -/
abbrev Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticSpace (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) := ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints V.toOver

/-- The common complex dimension of the smooth variety, computed from its
function-field differentials. -/
abbrev Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexDimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : ℕ :=
  Betti.AffineDimension.Realization.functionFieldDifferentialDimension V.structureMap

/-- The coordinate model of the proved analytic atlas. -/
abbrev Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticModel (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) := Fin V.complexDimension → ℂ

/-- The named dimension is the actual smooth relative dimension of the
structure morphism. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.smoothOfRelativeDimension_complexDimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    SmoothOfRelativeDimension V.complexDimension V.structureMap :=
  Betti.SmoothDimension.Realization.smoothOfFunctionFieldDimension V.structureMap

instance Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticSpace_nonempty (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : Nonempty V.analyticSpace :=
  V.complexPoints_nonempty

instance Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticSpace_compactSpace (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    CompactSpace V.analyticSpace :=
  Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.complexPoints_compactSpace V.presentation

instance Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticSpace_t2Space (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : T2Space V.analyticSpace :=
  Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.complexPoints_t2Space V.presentation

instance Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticSpace_secondCountableTopology (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    SecondCountableTopology V.analyticSpace :=
  Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.complexPoints_secondCountableTopology V.presentation

/-- These are the regular charts constructed on the native scheme points. -/
instance Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticSpace_chartedSpace (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    ChartedSpace V.analyticModel V.analyticSpace := by
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  exact ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeChartedSpace V.toOver

/-- The algebraic smoothness theorem gives complex analytic regularity of the
atlas, hence every differentiability order. -/
instance Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticSpace_complexIsManifold (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (r : ℕ∞ω) :
    IsManifold (𝓘(ℂ, V.analyticModel)) r V.analyticSpace := by
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  exact ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeComplexIsManifold V.toOver r

/-- The same proved atlas is the underlying real manifold used for
complex-valued differential forms. -/
instance Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticSpace_realIsManifold (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (r : ℕ∞ω) :
    IsManifold (𝓘(ℝ, V.analyticModel)) r V.analyticSpace := by
  let : IsIntegral V.toOver.left := V.property
  let : Smooth V.toOver.hom := V.presentation.smooth
  exact ComplexPoints.Analytic.IntrinsicSmoothSchemeManifold.nativeSmoothSchemeRealIsManifold V.toOver r

/-- The model has exactly the derived complex dimension. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticModel_complex_finrank (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Module.finrank ℂ V.analyticModel = V.complexDimension := by
  rw [Module.finrank_pi, Fintype.card_fin]

/-- The underlying real manifold has twice the complex dimension. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.analyticModel_real_finrank (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Module.finrank ℝ V.analyticModel = 2 * V.complexDimension := by
  rw [finrank_real_of_complex, V.analyticModel_complex_finrank]

end

end OAI.AlgebraicGeometry
