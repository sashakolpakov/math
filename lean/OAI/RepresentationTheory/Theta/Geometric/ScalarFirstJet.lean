import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.RingTheory.DualNumber
import Mathlib.Analysis.Complex.Basic

/-! # Scalar First Jet -/

namespace OAI.RepresentationTheory.Theta.Geometric.ScalarFirstJet

noncomputable section

/-! Actual first-order scalar jets in the complex dual-number ring. -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

def scalarFirstJet (f : V → ℂ) (z a : V) : DualNumber ℂ :=
  (f z, fderiv ℂ f z a)

theorem scalarFirstJet_const (c : ℂ) (z a : V) :
    scalarFirstJet (fun _ => c) z a = TrivSqZeroExt.inl c := by
  apply TrivSqZeroExt.ext
  · rfl
  · simp [scalarFirstJet]

theorem scalarFirstJet_mul (f g : V → ℂ) (z a : V)
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) :
    scalarFirstJet (fun w => f w * g w) z a = scalarFirstJet f z a * scalarFirstJet g z a := by
  apply TrivSqZeroExt.ext
  · rfl
  · change fderiv ℂ (fun w => f w * g w) z a = f z * fderiv ℂ g z a + fderiv ℂ f z a * g z
    rw [fderiv_fun_mul hf hg]
    simp [mul_comm]

theorem scalarFirstJet_inv (f : V → ℂ) (z a : V)
    (hf : DifferentiableAt ℂ f z) (hz : f z ≠ 0) :
    scalarFirstJet (fun w => (f w)⁻¹) z a = (scalarFirstJet f z a)⁻¹ := by
  apply TrivSqZeroExt.ext
  · rfl
  · have H := ((hasFDerivAt_inv' (𝕜 := ℂ) hz).comp z hf.hasFDerivAt).fderiv
    have H' := congrArg (fun d : V →L[ℂ] ℂ => d a) H
    change fderiv ℂ (fun w => (f w)⁻¹) z a =
      -((f z)⁻¹ * fderiv ℂ f z a * (f z)⁻¹)
    simpa [Function.comp_def, ContinuousLinearMap.mulLeftRight_apply, smul_eq_mul, mul_assoc] using H'

theorem scalarFirstJet_add_const (f : V → ℂ) (z a b : V) :
    scalarFirstJet (fun w => f (w + b)) z a = scalarFirstJet f (z + b) a := by
  apply TrivSqZeroExt.ext
  · rfl
  · exact congrArg (fun d : V →L[ℂ] ℂ => d a) (fderiv_comp_add_right b)

theorem scalarFirstJet_isUnit (f : V → ℂ) (z a : V) (hf : f z ≠ 0) :
    IsUnit (scalarFirstJet f z a) :=
  TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (isUnit_iff_ne_zero.mpr hf)

theorem scalarFirstJet_div (f g : V → ℂ) (z a : V)
    (hf : DifferentiableAt ℂ f z) (hg : DifferentiableAt ℂ g z) (hz : g z ≠ 0) :
    scalarFirstJet (fun w => f w / g w) z a =
      scalarFirstJet f z a * (scalarFirstJet g z a)⁻¹ := by
  simp only [div_eq_mul_inv]
  rw [scalarFirstJet_mul f (fun w => (g w)⁻¹) z a hf (hg.fun_inv hz),
    scalarFirstJet_inv g z a hg hz]

theorem scalarFirstJet_translates (f J : V → ℂ) (l z a : V)
    (hf : DifferentiableAt ℂ f z) (hJ : DifferentiableAt ℂ J z)
    (htrans : ∀ w, f (w + l) = J w * f w) :
    scalarFirstJet f (z + l) a = scalarFirstJet J z a * scalarFirstJet f z a := by
  rw [← scalarFirstJet_add_const f z a l, funext htrans]
  exact scalarFirstJet_mul J f z a hJ hf

end

end OAI.RepresentationTheory.Theta.Geometric.ScalarFirstJet
