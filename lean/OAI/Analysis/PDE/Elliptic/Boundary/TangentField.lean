import OAI.Analysis.PDE.Elliptic.Boundary.Flattening
import OAI.Analysis.PDE.Elliptic.Boundary.FieldCalculus

/-! Explicit tangent fields associated to a regular level set. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def levelTangentField (r : E → ℝ) (w e : E) (x : E) : E :=
  e - (fderiv ℝ r x e / fderiv ℝ r x w) • w

theorem levelTangentField_tangent (r : E → ℝ) (w e x : E)
    (hw : fderiv ℝ r x w ≠ 0) : fderiv ℝ r x (levelTangentField r w e x) = 0 := by
  simp only [levelTangentField, map_sub, map_smul, smul_eq_mul]
  rw [div_mul_cancel₀ _ hw, sub_self]

theorem contDiffAt_levelTangentField {r : E → ℝ} {x : E} (hr : ContDiffAt ℝ 3 r x)
    (w e : E) (hw : fderiv ℝ r x w ≠ 0) : ContDiffAt ℝ 2 (levelTangentField r w e) x := by
  have hd := hr.fderiv_right (m := 2) (by norm_num)
  exact contDiffAt_const.sub (((hd.clm_apply contDiffAt_const).div
    (hd.clm_apply contDiffAt_const) hw).smul contDiffAt_const)

theorem levelTangentField_at_base (r : E → ℝ) (w e x : E)
    (he : fderiv ℝ r x e = 0) : levelTangentField r w e x = e := by
  simp [levelTangentField, he]

theorem fieldDerivative_levelTangentField_zero [CompleteSpace E]
    {r u : E → ℝ} {x : E} (hr : ContDiffAt ℝ 1 r x) (hu : DifferentiableAt ℝ u x)
    (w e : E) (hw : fderiv ℝ r x w ≠ 0)
    (hzero : ∀ᶠ y in 𝓝 x, r y = r x → u y = 0) :
    fieldDerivative u (levelTangentField r w e) x = 0 := by
  have hne : fderiv ℝ r x ≠ 0 := by
    intro hz
    exact hw (by simp [hz])
  exact OAI.Analysis.PDE.Dirichlet.level_set_derivative_zero (hr.hasStrictFDerivAt (by norm_num)) hne
    hu.hasFDerivAt hzero (levelTangentField_tangent r w e x hw)

/-- This tangent field is exactly the inverse Jacobian applied to a tangent
coordinate vector for the chosen flattening map. -/
theorem flatteningMap_derivative_tangent {r : E → ℝ} {x y : E}
    (hr : DifferentiableAt ℝ r y) (g : E →L[ℝ] ℝ) (w e : E)
    (hgw : g w = 1) (he : g e = 0) (hw : fderiv ℝ r y w ≠ 0) :
    fderiv ℝ (flatteningMap r x g w) y (levelTangentField r w e y) = e := by
  have hd : HasFDerivAt (flatteningMap r x g w)
      (ContinuousLinearMap.id ℝ E + ((fderiv ℝ r y - g).smulRight w)) y := by
    convert ((hasFDerivAt_id y).sub_const x).add
      (((hr.hasFDerivAt.sub_const (r x)).sub
        (g.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x))).smul_const w) using 1 <;>
      simp [ContinuousLinearMap.comp_id]
    ext z
    simp [flatteningMap]
  rw [hd.fderiv]
  simp only [add_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply,
    sub_apply, levelTangentField_tangent r w e y hw]
  simp only [levelTangentField, map_sub, map_smul, he, hgw, smul_eq_mul, mul_one,
    zero_sub, neg_neg, sub_add_cancel]

end OAI.Analysis.PDE.Elliptic
