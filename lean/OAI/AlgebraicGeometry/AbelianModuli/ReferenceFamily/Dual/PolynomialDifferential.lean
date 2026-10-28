import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialDerivative

/-! # Polynomial Differential -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PolynomialDifferential

noncomputable section

section

/-! Evaluation on actual dual numbers computes the native analytic
differential of polynomial coordinates. -/

open OAI.AlgebraicGeometry.ComplexPoints.Analytic.PolynomialDerivative

variable {ι : Type*} [Fintype ι]

def dualPolynomialEvaluation (x v : ι → ℂ) : MvPolynomial ι ℂ →ₐ[ℂ] DualNumber ℂ :=
  MvPolynomial.aeval (fun i => (⟨x i, v i⟩ : DualNumber ℂ))

omit [Fintype ι] in
theorem dualPolynomialEvaluation_X (x v : ι → ℂ) (i : ι) :
    dualPolynomialEvaluation x v (MvPolynomial.X i) = (⟨x i, v i⟩ : DualNumber ℂ) :=
  MvPolynomial.aeval_X _ _

omit [Fintype ι] in
theorem dualPolynomialEvaluation_fst (x v : ι → ℂ) (p : MvPolynomial ι ℂ) :
    (dualPolynomialEvaluation x v p).fst = MvPolynomial.eval x p := by
  have he : (TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp (dualPolynomialEvaluation x v) =
      MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro i
    exact (congrArg TrivSqZeroExt.fst (dualPolynomialEvaluation_X x v i)).trans
      (MvPolynomial.aeval_X x i).symm
  exact DFunLike.congr_fun he p

theorem dualPolynomialEvaluation_snd (x v : ι → ℂ) (p : MvPolynomial ι ℂ) :
    (dualPolynomialEvaluation x v p).snd =
      fderiv ℂ (fun y : ι → ℂ => MvPolynomial.eval y p) x v := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      have hc : dualPolynomialEvaluation x v (MvPolynomial.C c) = (⟨c, 0⟩ : DualNumber ℂ) :=
        (dualPolynomialEvaluation x v).commutes c
      have hd : fderiv ℂ (fun y : ι → ℂ => MvPolynomial.eval y (MvPolynomial.C c)) x = 0 := by
        simpa only [MvPolynomial.eval_C] using (hasFDerivAt_const c x).fderiv
      exact (congrArg TrivSqZeroExt.snd hc).trans
        (congrArg (fun f : (ι → ℂ) →L[ℂ] ℂ => f v) hd).symm
  | add p q hp hq =>
      simp only [map_add, TrivSqZeroExt.snd_add]
      rw [fderiv_fun_add (ComplexPoints.Analytic.PolynomialDerivative.differentiable_polynomial_eval p x) (ComplexPoints.Analytic.PolynomialDerivative.differentiable_polynomial_eval q x)]
      exact congrArg₂ (fun a b : ℂ => a + b) hp hq
  | mul_X p i hp =>
      rw [map_mul, DualNumber.snd_mul, dualPolynomialEvaluation_fst, dualPolynomialEvaluation_X, hp]
      simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X]
      rw [fderiv_fun_mul (ComplexPoints.Analytic.PolynomialDerivative.differentiable_polynomial_eval p x) (differentiableAt_apply i x),
        (hasFDerivAt_apply i x).fderiv]
      change MvPolynomial.eval x p * v i +
        fderiv ℂ (fun y : ι → ℂ => MvPolynomial.eval y p) x v * x i =
        MvPolynomial.eval x p * v i + x i *
          fderiv ℂ (fun y : ι → ℂ => MvPolynomial.eval y p) x v
      ring

theorem dualPolynomialEvaluation_eq_zero_iff (x v : ι → ℂ) (p : MvPolynomial ι ℂ) :
    dualPolynomialEvaluation x v p = 0 ↔ MvPolynomial.eval x p = 0 ∧
      fderiv ℂ (fun y : ι → ℂ => MvPolynomial.eval y p) x v = 0 := by
  constructor
  · intro h
    exact ⟨(dualPolynomialEvaluation_fst x v p).symm.trans (congrArg TrivSqZeroExt.fst h),
      (dualPolynomialEvaluation_snd x v p).symm.trans (congrArg TrivSqZeroExt.snd h)⟩
  · rintro ⟨hf, hs⟩
    apply TrivSqZeroExt.ext
    · exact (dualPolynomialEvaluation_fst x v p).trans hf
    · exact (dualPolynomialEvaluation_snd x v p).trans hs

end

/-! Dual-number points of affine space over a fixed actual complex
point are precisely tangent vectors, with their actual reduction map. -/

variable {ι : Type*}

def DualPolynomialPoints (x : ι → ℂ) :=
  {f : MvPolynomial ι ℂ →ₐ[ℂ] DualNumber ℂ //
    (TrivSqZeroExt.fstHom ℂ ℂ ℂ).comp f = MvPolynomial.aeval x}

def dualPolynomialPoint (x v : ι → ℂ) : DualPolynomialPoints x :=
  ⟨dualPolynomialEvaluation x v, by
    apply AlgHom.ext
    intro p
    exact dualPolynomialEvaluation_fst x v p⟩

theorem dualPolynomialPoint_coordinates (x : ι → ℂ) (f : DualPolynomialPoints x) :
    dualPolynomialEvaluation x (fun i => (f.val (MvPolynomial.X i)).snd) = f.val := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [dualPolynomialEvaluation_X]
  apply TrivSqZeroExt.ext
  · have h := DFunLike.congr_fun f.property (MvPolynomial.X i)
    change (f.val (MvPolynomial.X i)).fst = (MvPolynomial.aeval x) (MvPolynomial.X i) at h
    exact (h.trans (MvPolynomial.aeval_X _ _)).symm
  · rfl

def dualPolynomialPointsEquiv (x : ι → ℂ) : (ι → ℂ) ≃ DualPolynomialPoints x where
  toFun := dualPolynomialPoint x
  invFun f i := (f.val (MvPolynomial.X i)).snd
  left_inv v := by
    funext i
    exact congrArg TrivSqZeroExt.snd (dualPolynomialEvaluation_X x v i)
  right_inv f := Subtype.ext (dualPolynomialPoint_coordinates x f)

theorem dualPolynomialPoint_scale (x v : ι → ℂ) (z : ℂ) :
    (LieRanks.dualNumberScale ℂ z).comp (dualPolynomialPoint x v).val =
      (dualPolynomialPoint x (z • v)).val := by
  apply MvPolynomial.algHom_ext
  intro i
  change LieRanks.dualNumberScale ℂ z (dualPolynomialEvaluation x v (MvPolynomial.X i)) =
    dualPolynomialEvaluation x (z • v) (MvPolynomial.X i)
  rw [dualPolynomialEvaluation_X, dualPolynomialEvaluation_X]
  exact TrivSqZeroExt.ext
    (TrivSqZeroExt.fst_map (z • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) (⟨x i, v i⟩ : DualNumber ℂ))
    (TrivSqZeroExt.snd_map (z • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) (⟨x i, v i⟩ : DualNumber ℂ))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PolynomialDifferential
