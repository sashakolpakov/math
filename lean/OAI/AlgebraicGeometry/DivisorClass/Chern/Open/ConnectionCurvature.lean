import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.OneFormProduct
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarExterior

/-! # Connection Curvature -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ConnectionCurvature

noncomputable section

/-! The actual local connection on one-forms has square equal to multiplication by its curvature. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {U W : Opens M} {p q : ℕ}

local instance connectionCurvature_tangentNormedGroup (x : M) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (NormedAddCommGroup E)

local instance connectionCurvature_tangentNormedSpace (x : M) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
  inferInstanceAs (NormedSpace ℝ E)

theorem openManifoldWedge_scalar_left (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U p) (b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U q) :
    ManifoldWedge.openManifoldWedge (SmoothScalarForm.smoothScalarOpenFormMul f a) b = SmoothScalarForm.smoothScalarOpenFormMul f (ManifoldWedge.openManifoldWedge a b) := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  rw [ManifoldWedge.openManifoldWedge_apply, SmoothScalarForm.smoothScalarOpenFormMul_apply, SmoothScalarForm.smoothScalarOpenFormMul_apply,
    ManifoldWedge.openManifoldWedge_apply, AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions.covectorWedge_smul_left]

theorem openManifoldWedge_scalar_right (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U)
    (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U p) (b : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U q) :
    ManifoldWedge.openManifoldWedge a (SmoothScalarForm.smoothScalarOpenFormMul f b) = SmoothScalarForm.smoothScalarOpenFormMul f (ManifoldWedge.openManifoldWedge a b) := by
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  rw [ManifoldWedge.openManifoldWedge_apply, SmoothScalarForm.smoothScalarOpenFormMul_apply, SmoothScalarForm.smoothScalarOpenFormMul_apply,
    ManifoldWedge.openManifoldWedge_apply, AlgebraicTopology.Kunneth.WedgeAlgebra.Constructions.covectorWedge_smul_right]

def openConnectionDerivativeOne (A : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1 →ₗ[ℂ] Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 2 :=
  Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d + ManifoldWedge.openManifoldWedgeRight A

theorem openConnectionDerivativeOne_apply (A a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1) :
    openConnectionDerivativeOne A a = Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a + ManifoldWedge.openManifoldWedge A a := rfl

theorem openConnectionDerivativeOne_restrict (h : W ≤ U) (A a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h (openConnectionDerivativeOne A a) =
      openConnectionDerivativeOne (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h A) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a) := by
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d a + ManifoldWedge.openManifoldWedge A a) =
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a) +
      ManifoldWedge.openManifoldWedge (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h A) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h a)
  exact ((Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h).map_add _ _).trans
    (congrArg₂ (fun b c => b + c) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_d h a) (ManifoldWedge.openManifoldWedge_restrict h A a))

theorem openConnectionDerivativeOne_exp_gauge (A B a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1)
    (l : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U)
    (hA : A = B + Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm l)) :
    openConnectionDerivativeOne B (SmoothScalarForm.smoothScalarOpenFormMul (SmoothScalarExterior.smoothComplexOpenFunctionExp l) a) =
      SmoothScalarForm.smoothScalarOpenFormMul (SmoothScalarExterior.smoothComplexOpenFunctionExp l) (openConnectionDerivativeOne A a) := by
  rw [openConnectionDerivativeOne_apply, openConnectionDerivativeOne_apply,
    OneFormProduct.smoothScalarOpenOneForm_d_mul, SmoothScalarExterior.smoothScalarOpenZeroForm_d_exp, hA,
    openManifoldWedge_scalar_left, openManifoldWedge_scalar_right, ManifoldWedge.openManifoldWedge_add_left]
  simp only [map_add]
  abel

theorem openConnectionDerivative_square_scalar (A : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1)
    (f : SmoothScalarForm.SmoothComplexOpenFunction (E := E) U) :
    openConnectionDerivativeOne A (SmoothScalarExterior.openConnectionDerivative A (SmoothScalarForm.smoothScalarOpenZeroForm f)) =
      SmoothScalarForm.smoothScalarOpenFormMul f (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d A) := by
  rw [SmoothScalarExterior.openConnectionDerivative_scalar, openConnectionDerivativeOne_apply, map_add,
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d_squared, zero_add, OneFormProduct.smoothScalarOpenOneForm_d_mul,
    ManifoldWedge.openManifoldWedge_add_right, openManifoldWedge_scalar_right, OneFormWedgeEvaluation.openManifoldWedge_one_one_self,
    map_zero, add_zero, OneFormWedgeEvaluation.openManifoldWedge_one_one_antisymm (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (SmoothScalarForm.smoothScalarOpenZeroForm f)) A]
  abel

theorem openConnectionDerivative_square (A : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 1) (a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U 0) :
    openConnectionDerivativeOne A (SmoothScalarExterior.openConnectionDerivative A a) = SmoothScalarExterior.openZeroFormMul (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d A) a := by
  have hz := ZeroFormFunctions.smoothScalarOpenZeroForm_openZeroFormFunction a
  exact (congrArg (fun b => openConnectionDerivativeOne A (SmoothScalarExterior.openConnectionDerivative A b)) hz).symm.trans
    (openConnectionDerivative_square_scalar A (ZeroFormFunctions.openZeroFormFunction a))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.ConnectionCurvature
