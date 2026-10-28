import OAI.AlgebraicGeometry.DivisorClass.Chern.SmoothScalarExterior
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Connection
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicLine.AntiForms

/-! # Covariant Derivative -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The actual smooth Chern covariant derivative on sections of the original holomorphic line bundle. -/

open _root_.TopologicalSpace _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {u : Holomorphic.Connecting.holomorphicUnitCohomology E M} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) (U : Opens M)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.covariantDerivative_compatible (s : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0) :
    (fun i => SmoothScalarExterior.openConnectionDerivative (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_right (h.localConnection i)) (s.val i)) ∈
      HolomorphicLine.AntiForms.holomorphicLineSmoothFormSubmodule u U 1 := by
  intro i j x hx hi hj
  obtain ⟨Z, hZ, hxZ, l, hl⟩ := Holomorphic.ExponentialEpi.exists_holomorphicSubopenLog (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j) ⟨x, hi, hj⟩
  let W := U ⊓ Z
  have hWF : W ≤ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j :=
    inf_le_right.trans hZ
  have hWi : W ≤ U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u i := fun _ hy => ⟨hy.1, (hZ hy.2).1⟩
  have hWj : W ≤ U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain E M u j := fun _ hy => ⟨hy.1, (hZ hy.2).2⟩
  let lW : Holomorphic.Exponential.HolomorphicFunction (E := E) (M := W) :=
    (Holomorphic.Sheaves.holomorphicFunctionSheaf E M).obj.map (homOfLE (show W ≤ Z from inf_le_right)).op l
  have hlW (y : W) : (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨y.val, hWF y.property⟩ =
      Complex.exp (lW y) := (hl ⟨y.val, y.property.2⟩).symm
  let L := SmoothHolomorphicScalar.holomorphicFunctionAsSmoothOpen lW
  have hs : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hWj (s.val j) =
      SmoothScalarForm.smoothScalarOpenFormMul (SmoothScalarExterior.smoothComplexOpenFunctionExp L) (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hWi (s.val i)) := by
    apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
    intro y
    rw [SmoothScalarForm.smoothScalarOpenFormMul_apply]
    change s.val j ⟨y.val, y.property.1, (hZ y.property.2).2⟩ =
      Complex.exp (lW y) • s.val i ⟨y.val, y.property.1, (hZ y.property.2).1⟩
    rw [← hlW y]
    exact s.property i j y.val y.property.1 (hWF y.property).1 (hWF y.property).2
  have hconn := h.localConnection_log_overlap i j W hWF lW hlW
  have hd : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hWj
      (SmoothScalarExterior.openConnectionDerivative (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_right (h.localConnection j)) (s.val j)) =
      SmoothScalarForm.smoothScalarOpenFormMul (SmoothScalarExterior.smoothComplexOpenFunctionExp L)
        (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict hWi
          (SmoothScalarExterior.openConnectionDerivative (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_right (h.localConnection i)) (s.val i))) := by
    rw [SmoothScalarExterior.openConnectionDerivative_restrict, SmoothScalarExterior.openConnectionDerivative_restrict,
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_trans, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_trans, hs]
    exact SmoothScalarExterior.openConnectionDerivative_exp_gauge_form _ _ L _ hconn
  have hv := congrArg (fun a : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E W 1 => a ⟨x, hx, hxZ⟩) hd
  simpa only [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_apply, SmoothScalarForm.smoothScalarOpenFormMul_apply,
    show (SmoothScalarExterior.smoothComplexOpenFunctionExp L) ⟨x, hx, hxZ⟩ =
      (Holomorphic.CohomologyTransitions.holomorphicCohomologyTransition E M u i j).val ⟨x, hi, hj⟩ from (hlW ⟨x, hx, hxZ⟩).symm] using hv

def HolomorphicMetric.Data.HolomorphicLineMetricData.covariantDerivative : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0 →ₗ[ℂ] HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1 where
  toFun s := ⟨fun i => SmoothScalarExterior.openConnectionDerivative
    (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_right (h.localConnection i)) (s.val i), h.covariantDerivative_compatible U s⟩
  map_add' s t := by
    apply Subtype.ext
    funext i
    exact (SmoothScalarExterior.openConnectionDerivative (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_right (h.localConnection i))).map_add (s.val i) (t.val i)
  map_smul' z s := by
    apply Subtype.ext
    funext i
    exact (SmoothScalarExterior.openConnectionDerivative (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_right (h.localConnection i))).map_smul z (s.val i)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.covariantDerivative_restrict {W : Opens M} (hWU : W ≤ U)
    (s : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 0) :
    HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict hWU (h.covariantDerivative U s) =
      h.covariantDerivative W (HolomorphicLine.AntiForms.holomorphicLineSmoothFormRestrict hWU s) := by
  apply Subtype.ext
  funext i
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (inf_le_inf_right _ hWU)
    (SmoothScalarExterior.openConnectionDerivative (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict inf_le_right (h.localConnection i)) (s.val i)) = _
  rw [SmoothScalarExterior.openConnectionDerivative_restrict, Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_trans]
  rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
