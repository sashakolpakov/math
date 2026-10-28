import OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultOpen
import OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultFunctionKernel
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Dolbeault Product -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DolbeaultProduct

noncomputable section

/-! The genuine coordinate Dolbeault differential commutes with multiplication by an actual holomorphic scalar. -/

open _root_.ContinuousAlternatingMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem complexAntilinearPart_holomorphic_smulRight (D : E →L[ℂ] ℂ) (a : F) :
    OAI.Analysis.DifferentialForms.Manifold.ComplexDerivativeParts.complexAntilinearPartCLM E F ((D.restrictScalars ℝ).smulRight a) = 0 := by
  have h : (D.restrictScalars ℝ).smulRight a = (D.smulRight a).restrictScalars ℝ := by
    ext v
    rfl
  rw [h]
  exact DolbeaultFunctionKernel.complexAntilinearPart_restrictScalars E F (D.smulRight a)

theorem extDerivDoublePrime_holomorphic_smul {n : ℕ} {g : E → ℂ} {a : OAI.Analysis.DifferentialForms.Manifold.Basic.RawForm E n} {x : E}
    (hg : DifferentiableAt ℂ g x) (ha : DifferentiableAt ℝ a x) :
    OAI.Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime (fun y => g y • a y) x = g x • OAI.Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime a x := by
  unfold OAI.Analysis.DifferentialForms.Manifold.DolbeaultLocal.extDerivDoublePrime
  rw [fderiv_fun_smul (hg.restrictScalars ℝ) ha, map_add, map_smul,
    hg.fderiv_restrictScalars ℝ, complexAntilinearPart_holomorphic_smulRight,
    add_zero, alternatizeUncurryFin_smul]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DolbeaultProduct
