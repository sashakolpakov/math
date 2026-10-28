import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.RoughSmooth
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.TensorIntegration

/-! # Covector Connection Support -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorConnectionSupport

noncomputable section

/-! Covariant differentiation preserves the support of a compactly supported smooth chart field. -/

open Filter
open scoped ContDiff _root_.Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Line.HessianBilinear.tensorConnection_formNormed Line.HessianBilinear.tensorConnection_formSpace
  Line.HessianBilinear.tensorConnection_oneNormed Line.HessianBilinear.tensorConnection_oneSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem lineCovectorConnectionDerivative_tsupport (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) :
    tsupport (Line.ConnectionSymbols.lineCovectorConnectionDerivative n G A a) ⊆ tsupport a := by
  apply closure_minimal _ (isClosed_tsupport a)
  intro x hx
  by_contra hxa
  apply hx
  apply ContinuousLinearMap.ext
  intro v
  exact Line.TensorIntegration.lineCovectorConnectionDerivative_off_support n G A a hxa v

theorem lineCovectorConnectionDerivative_global_smooth (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n)
    {U : Set E} (hU : IsOpen U) (hG : ContDiffOn ℝ ∞ G U) (hA : ContDiffOn ℝ ∞ A U)
    (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ U) :
    ContDiff ℝ ∞ (Line.ConnectionSymbols.lineCovectorConnectionDerivative n G A a) := by
  have hf := Line.CovectorNeg.lineCovectorConnectionDerivative_smoothOn n G A a hU hG hA ha.contDiffOn
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact hf.contDiffAt (hU.mem_nhds hx)
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp
      (fun ht => hx (hs (lineCovectorConnectionDerivative_tsupport n G A a ht))))

theorem lineCovectorConnectionDerivative_column_tsupport (n : ℕ)
    (G : E → E →L[ℝ] E →L[ℝ] E) (A : E → E →L[ℝ] ℂ) (a : E → Analysis.DifferentialForms.Manifold.Basic.FormValue E n) (v : E) :
    tsupport (fun x => Line.ConnectionSymbols.lineCovectorConnectionDerivative n G A a x v) ⊆ tsupport a := by
  apply closure_minimal _ (isClosed_tsupport a)
  intro x hx
  by_contra hxa
  exact hx (Line.TensorIntegration.lineCovectorConnectionDerivative_off_support n G A a hxa v)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CovectorConnectionSupport
