import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps
import OAI.Analysis.DifferentialForms.Manifold.Holomorphic
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! # Intrinsic Derivative Scalars -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars

noncomputable section

/-!
# Real and complex derivatives in the same genuine manifold charts

For a complex differentiable manifold map, the real derivative is precisely
the restriction of its complex derivative. The proof computes both actual
manifold derivatives in their shared preferred charts and invokes the ordinary
Fréchet derivative scalar-restriction theorem. The native scheme-point case
then follows from the proved analyticity of actual scheme morphisms.
-/

open scoped ContDiff _root_.Manifold
open _root_.CategoryTheory _root_.AlgebraicGeometry ChartedSpace

section Generic

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
variable [IsScalarTower ℝ ℂ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
variable [IsScalarTower ℝ ℂ F]
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace E M]
variable [TopologicalSpace N] [ChartedSpace F N]

set_option backward.isDefEq.respectTransparency false in
/-- In the same actual preferred charts, the real manifold derivative of a
complex `C¹` map is the scalar restriction of its complex manifold derivative.
The displayed model identifications are the defining tangent-space synonyms. -/
theorem real_mfderiv_eq_complex_restrictScalars {f : M → N} {x : M}
    (hf : ContMDiffAt (𝓘(ℂ, E)) (𝓘(ℂ, F)) 1 f x) :
    (show E →L[ℝ] F from mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x) =
      (show E →L[ℂ] F from mfderiv (𝓘(ℂ, E)) (𝓘(ℂ, F)) f x).restrictScalars ℝ := by
  have hc := hf.mdifferentiableAt one_ne_zero
  have hr := (OAI.Analysis.DifferentialForms.Manifold.Holomorphic.contMDiffAt_real_of_complex hf).mdifferentiableAt one_ne_zero
  let c : E → F := fun z => chartAt F (f x) (f ((chartAt E x).symm z))
  have hcd : DifferentiableAt ℂ c (chartAt E x x) := by
    simpa only [c, writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_def, id_eq, Set.range_id, differentiableWithinAt_univ]
      using hc.differentiableWithinAt_writtenInExtChartAt
  have hcr : (show E →L[ℝ] F from mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x) =
      fderiv ℝ c (chartAt E x x) := by
    simpa only [c, writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_def, id_eq, Set.range_id, fderivWithin_univ] using hr.mfderiv_abuse
  have hcc : (show E →L[ℂ] F from mfderiv (𝓘(ℂ, E)) (𝓘(ℂ, F)) f x) =
      fderiv ℂ c (chartAt E x x) := by
    simpa only [c, writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_def, id_eq, Set.range_id, fderivWithin_univ] using hc.mfderiv_abuse
  rw [hcr, hcc]
  exact hcd.fderiv_restrictScalars ℝ

set_option backward.isDefEq.respectTransparency false in
/-- The same identity on actual tangent vectors, through the defining model
identifications. This form is convenient for identifying tangent ranges. -/
theorem real_mfderiv_apply_eq_complex {f : M → N} {x : M}
    (hf : ContMDiffAt (𝓘(ℂ, E)) (𝓘(ℂ, F)) 1 f x) (v : E) :
    (mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, F)) f x) v =
      (mfderiv (𝓘(ℂ, E)) (𝓘(ℂ, F)) f x) v := by
  exact congrArg (fun L : E →L[ℝ] F => L v) (real_mfderiv_eq_complex_restrictScalars hf)

end Generic

variable {X Y : Over Foundations.Scheme.ProjectiveSpace.complexBase}
variable [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left] [Smooth Y.hom]

local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "ModelY" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)

set_option backward.isDefEq.respectTransparency false in
/-- The actual real derivative of an algebraic map on native complex points
is the restriction of its actual complex derivative. -/
theorem real_mfderiv_nativeScheme_map_eq_restrictScalars (φ : X ⟶ Y)
    (x : SchemePointHomeomorphs.schemeComplexPoints X) :
    (show ModelX →L[ℝ] ModelY from
      mfderiv (𝓘(ℝ, ModelX)) (𝓘(ℝ, ModelY)) (SchemePointHomeomorphs.schemeComplexPoints.map φ) x) =
      (show ModelX →L[ℂ] ModelY from
        mfderiv (𝓘(ℂ, ModelX)) (𝓘(ℂ, ModelY)) (SchemePointHomeomorphs.schemeComplexPoints.map φ) x).restrictScalars ℝ :=
  real_mfderiv_eq_complex_restrictScalars (IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map φ 1).contMDiffAt

set_option backward.isDefEq.respectTransparency false in
/-- Equality of the actual real and complex derivative values of a native
scheme map, used to identify its real and complex normal quotients. -/
theorem real_mfderiv_nativeScheme_map_apply (φ : X ⟶ Y)
    (x : SchemePointHomeomorphs.schemeComplexPoints X) (v : ModelX) :
    (mfderiv (𝓘(ℝ, ModelX)) (𝓘(ℝ, ModelY)) (SchemePointHomeomorphs.schemeComplexPoints.map φ) x) v =
      (mfderiv (𝓘(ℂ, ModelX)) (𝓘(ℂ, ModelY)) (SchemePointHomeomorphs.schemeComplexPoints.map φ) x) v :=
  real_mfderiv_apply_eq_complex (IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map φ 1).contMDiffAt v

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicDerivativeScalars
