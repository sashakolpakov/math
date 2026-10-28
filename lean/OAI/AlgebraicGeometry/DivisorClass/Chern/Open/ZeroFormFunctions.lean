import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarForm
import OAI.Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothPeriodMap

/-! # Zero Form Functions -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ZeroFormFunctions

noncomputable section

/-! Actual smooth scalar functions of the original ambient open zero-forms. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothPeriodMap.CM.Construction

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {U W : Opens M}

def openZeroFormFunction (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U :=
  ⟨ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.zeroFormScalar (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U 0 a),
    ComplexMultiplication.HodgeComparison.SmoothPeriodMap.CM.Construction.zeroFormScalar_contMDiff (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U 0 a)⟩

theorem openZeroFormFunction_apply (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) (x : U)
    (v : Fin 0 → TangentSpace 𝓘(ℝ, E) x.val) : openZeroFormFunction a x = a x v := by
  change (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E U 0 a) x 0 = a x v
  rw [Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_apply]
  change a x (fun _ => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) x 0) = a x v
  congr 1
  funext i
  exact Fin.elim0 i

theorem smoothScalarOpenZeroForm_openZeroFormFunction (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) :
    SmoothScalarForm.smoothScalarOpenZeroForm (openZeroFormFunction a) = a := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  rw [SmoothScalarForm.smoothScalarOpenZeroForm_apply, openZeroFormFunction_apply a x v]

theorem openZeroFormFunction_smoothScalarOpenZeroForm (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) :
    openZeroFormFunction (SmoothScalarForm.smoothScalarOpenZeroForm f) = f := by
  apply ContMDiffMap.ext
  intro x
  rw [openZeroFormFunction_apply _ x 0, SmoothScalarForm.smoothScalarOpenZeroForm_apply]

theorem openZeroFormFunction_add (a b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) :
    openZeroFormFunction (a + b) = openZeroFormFunction a + openZeroFormFunction b := by
  apply ContMDiffMap.ext
  intro x
  change openZeroFormFunction (a + b) x = openZeroFormFunction a x + openZeroFormFunction b x
  rw [openZeroFormFunction_apply _ x 0, openZeroFormFunction_apply _ x 0, openZeroFormFunction_apply _ x 0]
  rfl

theorem openZeroFormFunction_smul (z : ℂ) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) (x : U) :
    openZeroFormFunction (z • a) x = z * openZeroFormFunction a x := by
  rw [openZeroFormFunction_apply _ x 0, openZeroFormFunction_apply _ x 0]
  rfl

theorem openZeroFormFunction_restrict (h : W ≤ U) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) :
    openZeroFormFunction (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a) =
      SmoothScalarForm.smoothComplexOpenFunctionRestrict h (openZeroFormFunction a) := by
  apply ContMDiffMap.ext
  intro x
  change openZeroFormFunction (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a) x = openZeroFormFunction a ⟨x.val, h x.property⟩
  rw [openZeroFormFunction_apply _ x 0, openZeroFormFunction_apply _ ⟨x.val, h x.property⟩ 0]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ZeroFormFunctions
