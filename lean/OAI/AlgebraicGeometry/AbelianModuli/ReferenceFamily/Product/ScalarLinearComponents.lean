import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Module.Equiv.Basic

/-! # Scalar Linear Components -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ScalarLinearComponents

noncomputable section

/-! An equivalence linear over a product of fields acts separately
and linearly on each vector-space factor. The component maps and their
inverses are constructed from the actual equivalence. -/

open scoped Classical

variable {k I U : Type*} [Field k] [AddCommGroup U] [Module k U]

local notation "S" => I → k
local notation "W" => I → U

theorem piScalarLinear_coordinate_eq (f : W →ₗ[S] W) (p : I)
    (x y : W) (hxy : x p = y p) : f x p = f y p := by
  let e : S := Pi.single p 1
  have he : e • x = e • y := by
    ext q
    by_cases h : q = p
    · subst q
      simpa only [Pi.smul_apply', e, Pi.single_eq_same, one_smul] using hxy
    · simp only [Pi.smul_apply', e, Pi.single_eq_of_ne h, zero_smul]
  have h := congrArg (fun v : W => v p) (congrArg f he)
  rw [f.map_smul, f.map_smul] at h
  simpa only [Pi.smul_apply', e, Pi.single_eq_same, one_smul] using h

def piScalarLinearComponent (f : W ≃ₗ[S] W) (p : I) : U ≃ₗ[k] U where
  toFun x := f (fun _ => x) p
  invFun x := f.symm (fun _ => x) p
  left_inv x :=
    (piScalarLinear_coordinate_eq f.symm.toLinearMap p
      (fun _ => f (fun _ => x) p) (f (fun _ => x)) rfl).trans
        (congrArg (fun v : W => v p) (f.symm_apply_apply (fun _ => x)))
  right_inv x :=
    (piScalarLinear_coordinate_eq f.toLinearMap p
      (fun _ => f.symm (fun _ => x) p) (f.symm (fun _ => x)) rfl).trans
        (congrArg (fun v : W => v p) (f.apply_symm_apply (fun _ => x)))
  map_add' x y := congrArg (fun v : W => v p) (f.map_add (fun _ => x) (fun _ => y))
  map_smul' a x :=
    congrArg (fun v : W => v p) ((f.restrictScalars k).map_smul a (fun _ => x))

theorem piScalarLinearComponent_apply (f : W ≃ₗ[S] W) (p : I) (x : W) :
    f x p = piScalarLinearComponent f p (x p) :=
  piScalarLinear_coordinate_eq f.toLinearMap p x (fun _ => x p) rfl

def piComponentsScalarLinearEquiv (q : I → U ≃ₗ[k] U) : W ≃ₗ[S] W where
  toFun x p := q p (x p)
  invFun x p := (q p).symm (x p)
  left_inv x := by ext p; exact (q p).symm_apply_apply (x p)
  right_inv x := by ext p; exact (q p).apply_symm_apply (x p)
  map_add' x y := by ext p; exact (q p).map_add (x p) (y p)
  map_smul' a x := by ext p; exact (q p).map_smul (a p) (x p)

theorem piComponentsScalarLinearEquiv_components (f : W ≃ₗ[S] W) :
    piComponentsScalarLinearEquiv (piScalarLinearComponent f) = f := by
  ext x p
  exact (piScalarLinearComponent_apply f p x).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Product.ScalarLinearComponents
