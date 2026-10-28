import OAI.Analysis.PDE.Dirichlet.RealOperator
import OAI.Analysis.PDE.Dirichlet.LogSupport
import OAI.Analysis.PDE.Elliptic.UniformFrame

open Set InnerProductSpace
open scoped Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Elliptic

theorem traceRight_directional_sum
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {J : Type*} [Fintype J]
    (v : J → E) (a : J → ℝ) (T : E →L[ℝ] E)
    (hT : T = ∑ j, a j • rankOne ℝ (v j) (v j))
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x : E) :
    OAI.Analysis.PDE.Elliptic.traceRight (fderiv ℝ (gradient f) x) T =
      ∑ j, a j * directionalDerivative (directionalDerivative f (v j)) (v j) x := by
  rw [hT, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul, OAI.Analysis.PDE.Elliptic.traceRight_rankOne, smul_eq_mul, directionalDerivative_twice hf]
  congr 1
  calc
    inner ℝ (v j) (fderiv ℝ (gradient f) x (v j)) =
        inner ℝ (fderiv ℝ (gradient f) x (v j)) (v j) := real_inner_comm _ _
    _ = _ := OAI.Analysis.PDE.Elliptic.inner_fderiv_gradient hf x (v j) (v j)

/-- Concavity couples the actual second directional derivatives using the
coefficients of the real linearized operator at the second point. -/
theorem log_equation_weighted_difference {n : ℕ} {J : Type*} [Fintype J]
    {ψ F : CoordinateSpace n 4 → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (x y : CoordinateSpace n 4)
    (hx : (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (hy : (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y)).PosDef)
    (heqx : OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x)
    (heqy : OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y) = F y)
    (v : J → CoordinateSpace n 4) (a : J → ℝ)
    (hrep : logRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y) =
      ∑ j, a j • rankOne ℝ (v j) (v j)) :
    Real.log (F x) - Real.log (F y) ≤
      ∑ j, a j *
        (directionalDerivative (directionalDerivative ψ (v j)) (v j) x -
         directionalDerivative (directionalDerivative ψ (v j)) (v j) y) := by
  let A := quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y
  let B := quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x
  have hs := log_mooreDet_support A B hy hx
  have hsub : OAI.LinearAlgebra.Moore.mooreDifferential n A (B - A) =
      OAI.LinearAlgebra.Moore.mooreDifferential n A B - OAI.LinearAlgebra.Moore.mooreDifferential n A A :=
    (OAI.LinearAlgebra.Moore.mooreDifferentialLinear n A).map_sub B A
  have hval (z : CoordinateSpace n 4) :
      OAI.LinearAlgebra.Moore.mooreDifferential n A (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ z) / OAI.LinearAlgebra.Moore.mooreDet n A =
        ∑ j, a j * directionalDerivative (directionalDerivative ψ (v j)) (v j) z := by
    calc
      _ = logOperatorFunctional A (fderiv ℝ (gradient ψ) z) := by
        rw [logOperatorFunctional_apply, operatorCoordinateMatrix_fderiv_gradient hψ]
        rfl
      _ = OAI.Analysis.PDE.Elliptic.traceRight (fderiv ℝ (gradient ψ) z) (logRealOperator A) :=
        (OAI.Analysis.PDE.Elliptic.symmetricTraceDual_represents _ _ _ (OAI.Analysis.PDE.Elliptic.fderiv_gradient_isSymmetric hψ z)).symm
      _ = _ := traceRight_directional_sum v a (logRealOperator A) hrep hψ z
  rw [hsub, sub_div] at hs
  change Real.log (OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)) -
    Real.log (OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y)) ≤ _ at hs
  rw [hval x, hval y, heqx, heqy, ← Finset.sum_sub_distrib] at hs
  simpa only [mul_sub] using hs

/-- Twice differentiating the equation gives a subsolution for the very same
real operator whose positive direction decomposition is used above. -/
theorem log_equation_second_directional_ge {n : ℕ}
    {ψ F : CoordinateSpace n 4 → ℝ} (hψ : ContDiff ℝ 4 ψ)
    {Ω : Set (CoordinateSpace n 4)} (hΩ : IsOpen Ω)
    (hpos : ∀ x ∈ Ω, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x)).PosDef)
    (heq : ∀ x ∈ Ω, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) = F x)
    (v : CoordinateSpace n 4) {x : CoordinateSpace n 4} (hx : x ∈ Ω) :
    deriv (deriv (fun t : ℝ ↦ Real.log (F (x + t • v)))) 0 ≤
      OAI.Analysis.PDE.Elliptic.ellipticTrace (fun y ↦ logRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y))
        (directionalDerivative (directionalDerivative ψ v) v) x := by
  have hv3 : ContDiff ℝ 3 (directionalDerivative ψ v) :=
    contDiff_directionalDerivative hψ (by norm_num) v
  have hvv : ContDiff ℝ 2 (directionalDerivative (directionalDerivative ψ v) v) :=
    contDiff_directionalDerivative hv3 (by norm_num) v
  have hF : 0 < F x := by
    rw [← heq x hx]
    exact OAI.LinearAlgebra.Moore.mooreDet_pos_of_complexify_posDef _ (hpos x hx)
  rw [logRealOperator_linearization _ hvv, heq x hx]
  apply (le_div_iff₀ hF).mpr
  have h := mooreLinearization_second_directional_ge hψ hΩ hpos heq v hx
  simpa only [mul_comm] using h

end OAI.Analysis.PDE.Dirichlet
