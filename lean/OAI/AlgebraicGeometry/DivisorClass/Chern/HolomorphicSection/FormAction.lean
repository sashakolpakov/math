import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.AntiForms
import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarExterior

/-! # Form Action -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.FormAction

noncomputable section

/-! Multiplication of an original bundle section by an actual scalar differential form. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (u : Holomorphic.Connecting.holomorphicUnitCohomology E M) (U : Opens M) (n : ℕ)

def holomorphicSectionFormAction (A : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) :
    HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0 →ₗ[ℂ] HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U n where
  toFun a := ⟨fun i => SmoothScalarExterior.openZeroFormMul (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_left A) (a.val i), by
    intro i j x hx hi hj
    rw [SmoothScalarExterior.openZeroFormMul_apply, SmoothScalarExterior.openZeroFormMul_apply]
    have he := congrArg (fun b : TangentSpace 𝓘(ℝ, E) x [⋀^Fin 0]→L[ℝ] ℂ => b 0)
      (a.property i j x hx hi hj)
    change a.val j ⟨x, hx, hj⟩ 0 =
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hi, hj⟩ * a.val i ⟨x, hx, hi⟩ 0 at he
    change a.val j ⟨x, hx, hj⟩ 0 • A ⟨x, hx⟩ =
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hi, hj⟩ • (a.val i ⟨x, hx, hi⟩ 0 • A ⟨x, hx⟩)
    rw [he, mul_smul]⟩
  map_add' a b := by
    apply Subtype.ext
    funext i
    exact (SmoothScalarExterior.openZeroFormMul (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_left A)).map_add (a.val i) (b.val i)
  map_smul' z a := by
    apply Subtype.ext
    funext i
    exact (SmoothScalarExterior.openZeroFormMul (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_left A)).map_smul z (a.val i)

theorem holomorphicSectionFormAction_coordinate (A : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n)
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0) (i : M) :
    (holomorphicSectionFormAction u U n A a).val i =
      SmoothScalarExterior.openZeroFormMul (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_left A) (a.val i) := rfl

theorem holomorphicSectionFormAction_restrict {W : Opens M} (h : W ≤ U)
    (A : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E U n) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0) :
    HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict h (holomorphicSectionFormAction u U n A a) =
      holomorphicSectionFormAction u W n (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict h A) (HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict h a) := by
  apply Subtype.ext
  funext i
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (inf_le_inf_right _ h)
    (SmoothScalarExterior.openZeroFormMul (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_left A) (a.val i)) = _
  rw [SmoothScalarExterior.openZeroFormMul_restrict, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_trans]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.FormAction
