import OAI.Analysis.PDE.Dirichlet.Moore.RealOperator
import OAI.Analysis.PDE.Dirichlet.CoordinateTransport
import OAI.Analysis.PDE.Green.GreenCofactor

open Set InnerProductSpace _root_.MeasureTheory
open scoped Matrix.Norms.Elementwise MatrixOrder ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Green OAI.Analysis.PDE.Elliptic

/-- The real divergence-form coefficients of the actual Moore determinant.
They are polynomial in the quaternionic Hessian, with no inverse or
ellipticity hypothesis in their definition. -/
def mooreRealMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) Q) :
    Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ :=
  OAI.Analysis.Calculus.Quaternion.realCoefficients OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.LinearAlgebra.Moore.mooreCofactor n A)

theorem mooreRealMatrix_isSymm {n : ℕ} (A : Matrix (Fin n) (Fin n) Q) :
    (mooreRealMatrix A).IsSymm :=
  OAI.Analysis.Calculus.Quaternion.realCoefficients_isSymm OAI.Analysis.Calculus.Quaternion.fourSlots _ (OAI.LinearAlgebra.Moore.mooreCofactor_isHermitian n A)

theorem mooreRealMatrix_quadratic {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (v : CoordinateSpace n 4) :
    (∑ p, ∑ q, mooreRealMatrix A p q * (v p * v q)) =
      inner ℝ v (detRealOperator A v) := by
  rw [detRealOperator_symbol]
  change (∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.LinearAlgebra.Moore.mooreCofactor n A) p q * (v p * v q)) = _
  rw [OAI.Analysis.PDE.Green.realCoefficients_quadratic, ← OAI.LinearAlgebra.Moore.realTrace_mul_outer,
    OAI.LinearAlgebra.Moore.mooreCofactor_pairing n A _ (OAI.Analysis.Calculus.Quaternion.outer_isHermitian _)]

theorem mooreRealMatrix_elliptic_bounds {n : ℕ}
    (A : Matrix (Fin n) (Fin n) Q) (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef)
    {a B lam L : ℝ} (ha : 0 ≤ a) (hlam : 0 ≤ lam) (hL : 0 ≤ L)
    (hdet : a ≤ OAI.LinearAlgebra.Moore.mooreDet n A ∧ OAI.LinearAlgebra.Moore.mooreDet n A ≤ B)
    (hell : ∀ v : CoordinateSpace n 4,
      lam * ‖v‖ ^ 2 ≤ logPrincipalSymbol A v ∧ logPrincipalSymbol A v ≤ L * ‖v‖ ^ 2)
    (v : CoordinateSpace n 4) :
    (a * lam) * ‖v‖ ^ 2 ≤ (∑ p, ∑ q, mooreRealMatrix A p q * (v p * v q)) ∧
      (∑ p, ∑ q, mooreRealMatrix A p q * (v p * v q)) ≤ (B * L) * ‖v‖ ^ 2 := by
  rw [mooreRealMatrix_quadratic]
  exact detRealOperator_elliptic_bounds A hA ha hlam hL hdet hell v

theorem mooreRealMatrix_linearization_at {n : ℕ}
    (A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) Q)
    {w : CoordinateSpace n 4 → ℝ} {x : CoordinateSpace n 4}
    (hw : ContDiffAt ℝ 2 w x) :
    indexedNondivergenceOperator (fun y ↦ mooreRealMatrix (A y)) w x =
      mooreLinearization A w x := by
  change (∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.LinearAlgebra.Moore.mooreCofactor n (A x)) p q *
    realHessian w x p q) = _
  rw [← OAI.Analysis.PDE.Green.realTrace_hessianMap _ OAI.Analysis.Calculus.Quaternion.fourSlots _ (realHessian_isSymm hw)]
  exact OAI.LinearAlgebra.Moore.mooreCofactor_pairing n (A x) _ (quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots hw)

/-- The symmetric real coefficients have zero column divergence for every
C³ potential. This is the conservation law needed to identify the weak
variational equation with the nondivergence-form linearization. -/
theorem mooreRealMatrix_divergence {n : ℕ} {ψ : CoordinateSpace n 4 → ℝ}
    (hψ : ContDiff ℝ 3 ψ) (x : CoordinateSpace n 4) (q : Fin n × Fin 4) :
    (∑ p, fderiv ℝ (fun y ↦ mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y) p q)
      x (coordinateVector p)) = 0 := by
  have hA : ContDiff ℝ 1 (fun y ↦ OAI.LinearAlgebra.Moore.mooreCofactor n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y)) :=
    (OAI.LinearAlgebra.Moore.contDiff_mooreCofactor n 1).comp (OAI.Analysis.PDE.Green.contDiff_quaternionHessian_one OAI.Analysis.Calculus.Quaternion.fourSlots hψ)
  change (∑ p, fderiv ℝ (fun y ↦ OAI.Analysis.Calculus.Quaternion.realCoefficients OAI.Analysis.Calculus.Quaternion.fourSlots
    (OAI.LinearAlgebra.Moore.mooreCofactor n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y)) p q) x (coordinateVector p)) = 0
  simp_rw [OAI.Analysis.PDE.Green.fderiv_realCoefficient OAI.Analysis.Calculus.Quaternion.fourSlots _ _ (hA.differentiable one_ne_zero x)]
  exact OAI.Analysis.Calculus.Quaternion.realCoefficients_divergence_zero OAI.Analysis.Calculus.Quaternion.fourSlots _
    (fun b ↦ OAI.Analysis.Calculus.Quaternion.mooreCofactor_quaternionHessian_divergence OAI.Analysis.Calculus.Quaternion.fourSlots hψ.contDiffAt b) q

/-- Integration by parts for the actual real elliptic linearization, not an
abstract coefficient field supplied with a divergence-free assumption. -/
theorem detRealOperator_green {n : ℕ} {ψ u v : CoordinateSpace n 4 → ℝ}
    (hψ : ContDiff ℝ 3 ψ) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v)
    (hs : HasCompactSupport u) :
    (∫ x, u x * OAI.Analysis.PDE.Elliptic.ellipticTrace
      (fun y ↦ detRealOperator (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ y)) v x) =
      -(∫ x, ∑ p, ∑ q, mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots ψ x) p q *
        realGradient u x p * realGradient v x q) := by
  simp_rw [detRealOperator_linearization _ hv]
  exact OAI.Analysis.PDE.Green.moore_cofactor_green OAI.Analysis.Calculus.Quaternion.fourSlots hψ hu hv hs

end OAI.Analysis.PDE.Dirichlet
