import OAI.AlgebraicGeometry.FormalGeometry.Completion.NonnegativeQuadraticBilinear
import OAI.AlgebraicGeometry.FormalGeometry.Completion.RationalizationDetection
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct

/-! # Rational Quadratic Form -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! The rational quadratic form on the rationalization of an abelian group,
with positivity obtained by clearing denominators. -/

open scoped TensorProduct

universe u
variable {G : Type u} [AddCommGroup G] (q : NonnegativeQuadraticMk.Construction.NonnegativeQuadratic G)

def NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.rationalBilinear : LinearMap.BilinForm ℚ (TensorProduct ℤ ℚ G) :=
  (LinearMap.BilinMap.baseChange ℚ q.bilinear).compr₂
    (IsLocalization.moduleLid (nonZeroDivisors ℤ) ℚ ℚ).toLinearMap

theorem NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.rationalBilinear_tmul (r s : ℚ) (x y : G) :
    q.rationalBilinear (r ⊗ₜ[ℤ] x) (s ⊗ₜ[ℤ] y) = (r * s) * q.bilinear x y := rfl

def NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.rationalQuadraticForm : QuadraticForm ℚ (TensorProduct ℤ ℚ G) :=
  (1 / 2 : ℚ) • q.rationalBilinear.toQuadraticMap

theorem NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.rationalQuadraticForm_one_tmul (x : G) :
    q.rationalQuadraticForm ((1 : ℚ) ⊗ₜ[ℤ] x) = q.value x := by
  change (1 / 2 : ℚ) * q.rationalBilinear (1 ⊗ₜ[ℤ] x) (1 ⊗ₜ[ℤ] x) = _
  rw [NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.rationalBilinear_tmul, NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.bilinear_self]
  ring

theorem NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.rationalQuadraticForm_nonneg (x : TensorProduct ℤ ℚ G) : 0 ≤ q.rationalQuadraticForm x := by
  obtain ⟨n, g, hn, hg⟩ := RationalizationDetection.Construction.rationalization_exists_integer_multiple x
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hh : q.rationalQuadraticForm ((n : ℚ) • x) = q.value g := by
    change q.rationalQuadraticForm (n • x) = q.value g
    rw [hg, NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.rationalQuadraticForm_one_tmul]
  rw [QuadraticMap.map_smul, smul_eq_mul] at hh
  have hnpos : 0 < (n : ℚ) * n := mul_self_pos.mpr hnq
  exact (mul_nonneg_iff_of_pos_left hnpos).mp (hh.symm ▸ q.nonneg g)

theorem NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.rationalQuadraticForm_posDef (hzero : ∀ g, q.value g = 0 → g = 0) :
    q.rationalQuadraticForm.PosDef := by
  apply QuadraticMap.posDef_of_nonneg q.rationalQuadraticForm_nonneg
  intro x hx
  obtain ⟨n, g, hn, hg⟩ := RationalizationDetection.Construction.rationalization_exists_integer_multiple x
  have hh : q.value g = 0 := by
    rw [← NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.rationalQuadraticForm_one_tmul, ← hg]
    change q.rationalQuadraticForm ((n : ℚ) • x) = 0
    rw [QuadraticMap.map_smul, hx, smul_zero]
  rw [hzero g hh, TensorProduct.tmul_zero] at hg
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  change (n : ℚ) • x = 0 at hg
  have h := congrArg (fun y : TensorProduct ℤ ℚ G => (n : ℚ)⁻¹ • y) hg
  simpa only [smul_smul, inv_mul_cancel₀ hnq, one_smul, smul_zero] using h

theorem NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.rationalQuadraticForm_similitude (f : G →+ G) (c : ℚ)
    (hf : ∀ g, q.value (f g) = c * q.value g) (x : TensorProduct ℤ ℚ G) :
    q.rationalQuadraticForm (f.toIntLinearMap.baseChange ℚ x) = c * q.rationalQuadraticForm x := by
  have h : q.rationalQuadraticForm.comp (f.toIntLinearMap.baseChange ℚ) = c • q.rationalQuadraticForm := by
    apply _root_.baseChange_ext
    intro g
    change q.rationalQuadraticForm ((1 : ℚ) ⊗ₜ[ℤ] f g) = c * q.rationalQuadraticForm (1 ⊗ₜ[ℤ] g)
    rw [NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.rationalQuadraticForm_one_tmul, NonnegativeQuadraticMk.Construction.NonnegativeQuadratic.rationalQuadraticForm_one_tmul, hf]
  exact QuadraticMap.congr_fun h x

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
