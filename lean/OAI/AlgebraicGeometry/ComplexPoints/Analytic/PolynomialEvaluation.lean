import OAI.AlgebraicGeometry.ComplexPoints.Analytic.Affine
import Mathlib.Topology.Algebra.MvPolynomial

/-! # Polynomial Evaluation -/

namespace OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialEvaluation

noncomputable section

/-!
# Polynomial coordinates on affine complex points

The complex points of a polynomial algebra, with the topology induced by all
regular functions, are homeomorphic to the ordinary product of complex
coordinate spaces. This identifies the affine-point topology with the standard
Euclidean topology when the variable type is finite. No Zariski topology is used.
-/

universe u v

/-- A character of a polynomial algebra is uniquely determined by its coordinates. -/
def polynomialPointEquiv (ι : Type u) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial ι ℂ) ≃ (ι → ℂ) where
  toFun x i := x (MvPolynomial.X i)
  invFun z := MvPolynomial.aeval z
  left_inv x := (MvPolynomial.aeval_unique x).symm
  right_inv z := by
    funext i
    exact MvPolynomial.aeval_X z i

@[simp] theorem polynomialPointEquiv_apply {ι : Type u}
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial ι ℂ)) (i : ι) :
    polynomialPointEquiv ι x i = x (MvPolynomial.X i) := rfl

@[simp] theorem polynomialPointEquiv_symm_apply {ι : Type u}
    (z : ι → ℂ) (p : MvPolynomial ι ℂ) :
    (polynomialPointEquiv ι).symm z p = MvPolynomial.eval z p := rfl

/-- Evaluation in coordinates agrees with the given algebra character. -/
@[simp] theorem polynomialPointEquiv_eval {ι : Type u}
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial ι ℂ)) (p : MvPolynomial ι ℂ) :
    MvPolynomial.eval (polynomialPointEquiv ι x) p = x p :=
  (AlgHom.congr_fun (MvPolynomial.aeval_unique x) p).symm

/-- The topology defined by all polynomial evaluations is exactly the coordinate topology. -/
def polynomialPointHomeomorph (ι : Type u) :
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial ι ℂ) ≃ₜ (ι → ℂ) where
  toEquiv := polynomialPointEquiv ι
  continuous_toFun := continuous_pi fun i =>
    Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_eval (MvPolynomial.X i)
  continuous_invFun := by
    apply (Foundations.Scheme.AffineComplexPoints.affineComplexPoints.continuous_iff _).2
    intro p
    exact MvPolynomial.continuous_eval p

@[simp] theorem polynomialPointHomeomorph_apply {ι : Type u}
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial ι ℂ)) (i : ι) :
    polynomialPointHomeomorph ι x i = x (MvPolynomial.X i) := rfl

@[simp] theorem polynomialPointHomeomorph_symm_apply {ι : Type u}
    (z : ι → ℂ) (p : MvPolynomial ι ℂ) :
    (polynomialPointHomeomorph ι).symm z p = MvPolynomial.eval z p := rfl

/-- A family of polynomial coordinate functions defines a continuous map. -/
theorem continuous_polynomial_map {ι : Type u} {κ : Type v}
    (P : κ → MvPolynomial ι ℂ) :
    Continuous (fun z : ι → ℂ => fun j => MvPolynomial.eval z (P j)) :=
  continuous_pi fun j => MvPolynomial.continuous_eval (P j)

/-- Restricting a regular function to any affine coordinate subspace is continuous. -/
theorem continuous_polynomial_restriction {ι : Type u}
    (s : Set (ι → ℂ)) (p : MvPolynomial ι ℂ) :
    Continuous (fun z : s => MvPolynomial.eval (z : ι → ℂ) p) :=
  (MvPolynomial.continuous_eval p).comp continuous_subtype_val

/-- Algebraic substitution becomes the usual polynomial map in complex coordinates. -/
theorem polynomialPointEquiv_comp_aeval {ι : Type u} {κ : Type v}
    (x : Foundations.Scheme.AffineComplexPoints.affineComplexPoints (MvPolynomial ι ℂ))
    (P : κ → MvPolynomial ι ℂ) (j : κ) :
    polynomialPointEquiv κ (x.comp (MvPolynomial.aeval P)) j =
      MvPolynomial.eval (polynomialPointEquiv ι x) (P j) := by
  simp only [polynomialPointEquiv_apply, AlgHom.comp_apply, MvPolynomial.aeval_X,
    polynomialPointEquiv_eval]

end

end OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialEvaluation
