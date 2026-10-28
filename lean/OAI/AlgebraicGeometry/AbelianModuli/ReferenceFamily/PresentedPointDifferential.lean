import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PresentedAlgebra
import OAI.AlgebraicGeometry.Foundations.Scheme.StandardSmoothJacobian

/-! # Presented Point Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PresentedPointDifferential

noncomputable section

/-! Differentiating actual regular functions in presentation coordinates
constructs their genuine dual-number values. -/

variable {S ι σ U : Type*} [CommRing S] [Algebra ℂ S] [Fintype ι]
  [NormedAddCommGroup U] [NormedSpace ℂ U]

omit [Fintype ι] in
theorem presentedPoint_polynomial_eval (P : Algebra.Presentation ℂ S ι σ)
    (x : S →ₐ[ℂ] ℂ) (p : MvPolynomial ι ℂ) :
    MvPolynomial.eval (fun i => x (P.val i)) p = x (MvPolynomial.aeval P.val p) := by
  have hc : (Foundations.Scheme.PresentedComplexPoints.presentedComplexPointsEquiv P x).val = fun i => x (P.val i) :=
    funext (Foundations.Scheme.PresentedComplexPoints.presentedComplexPointsEquiv_apply P x)
  exact (congrArg (fun z => MvPolynomial.eval z p) hc).symm.trans (Foundations.Scheme.PresentedComplexPoints.presentedComplexPointsEquiv_eval P x p)

def presentedPointCoordinates (P : Algebra.Presentation ℂ S ι σ)
    (φ : U → Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) : U → (ι → ℂ) := fun u i => φ u (P.val i)

omit [Fintype ι] in
theorem presentedPointCoordinates_differentiable (P : Algebra.Presentation ℂ S ι σ)
    (φ : U → Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (u : U)
    (hφ : ∀ a : S, DifferentiableAt ℂ (fun w => φ w a) u) :
    DifferentiableAt ℂ (presentedPointCoordinates P φ) u :=
  differentiableAt_pi.mpr (fun i => hφ (P.val i))

theorem presentedPoint_polynomial_derivative (P : Algebra.Presentation ℂ S ι σ)
    (φ : U → Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (u v : U)
    (hφ : ∀ a : S, DifferentiableAt ℂ (fun w => φ w a) u) (p : MvPolynomial ι ℂ) :
    fderiv ℂ (fun w => φ w (MvPolynomial.aeval P.val p)) u v =
      fderiv ℂ (fun y : ι → ℂ => MvPolynomial.eval y p) (presentedPointCoordinates P φ u)
        (fderiv ℂ (presentedPointCoordinates P φ) u v) := by
  have hG := presentedPointCoordinates_differentiable P φ u hφ
  have hd := (ComplexPoints.Analytic.PolynomialDerivative.differentiable_polynomial_eval p (presentedPointCoordinates P φ u)).hasFDerivAt.comp
    u hG.hasFDerivAt
  have hd' : HasFDerivAt (fun w => φ w (MvPolynomial.aeval P.val p))
      ((fderiv ℂ (fun y : ι → ℂ => MvPolynomial.eval y p) (presentedPointCoordinates P φ u)).comp
        (fderiv ℂ (presentedPointCoordinates P φ) u)) u := by
    apply hd.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun w => (presentedPoint_polynomial_eval P (φ w) p).symm)
  exact DFunLike.congr_fun hd'.fderiv v

theorem presentedPoint_derivative_mem (P : Algebra.Presentation ℂ S ι σ)
    (φ : U → Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (u v : U)
    (hφ : ∀ a : S, DifferentiableAt ℂ (fun w => φ w a) u) :
    fderiv ℂ (presentedPointCoordinates P φ) u v ∈
      Dual.QuotientPoints.polynomialRelationTangent P.ker (fun i => φ u (P.val i)) := by
  apply (Dual.QuotientPoints.mem_polynomialRelationTangent _ _ _).mpr
  intro p hp
  have he : MvPolynomial.aeval P.val p = 0 := by
    rw [P.ker_eq_ker_aeval_val] at hp
    exact hp
  have h := presentedPoint_polynomial_derivative P φ u v hφ p
  have hz : (fun w => φ w (MvPolynomial.aeval P.val p)) = fun _ : U => (0 : ℂ) := by
    funext w
    rw [he, map_zero]
  rw [hz] at h
  exact h.symm.trans (DFunLike.congr_fun (hasFDerivAt_const (0 : ℂ) u).fderiv v)

def presentedDifferentialPoint (P : Algebra.Presentation ℂ S ι σ)
    (φ : U → Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (u v : U)
    (hφ : ∀ a : S, DifferentiableAt ℂ (fun w => φ w a) u) : Dual.PresentedAlgebra.DualAlgebraPoints (φ u) :=
  Dual.PresentedAlgebra.presentedDualPointsEquiv P (φ u)
    ⟨fderiv ℂ (presentedPointCoordinates P φ) u v, presentedPoint_derivative_mem P φ u v hφ⟩

theorem presentedDifferentialPoint_snd (P : Algebra.Presentation ℂ S ι σ)
    (φ : U → Foundations.Scheme.AffineComplexPoints.affineComplexPoints S) (u v : U)
    (hφ : ∀ a : S, DifferentiableAt ℂ (fun w => φ w a) u) (a : S) :
    ((presentedDifferentialPoint P φ u v hφ).val a).snd = fderiv ℂ (fun w => φ w a) u v := by
  have h := Dual.PresentedAlgebra.presentedDualPointsEquiv_eval P (φ u)
    ⟨fderiv ℂ (presentedPointCoordinates P φ) u v, presentedPoint_derivative_mem P φ u v hφ⟩ a
  have hd := presentedPoint_polynomial_derivative P φ u v hφ (P.σ a)
  rw [P.aeval_val_σ] at hd
  exact h.trans hd.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PresentedPointDifferential
