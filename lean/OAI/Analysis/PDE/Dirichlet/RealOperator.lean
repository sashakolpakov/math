import OAI.Analysis.PDE.Elliptic.TraceDual
import OAI.Analysis.PDE.Elliptic.TraceCoercivity
import OAI.Analysis.PDE.Dirichlet.EllipticData
import OAI.Analysis.PDE.Dirichlet.HessianMapNorm
import OAI.Analysis.PDE.Dirichlet.SecondDerivative

open InnerProductSpace
open scoped Matrix
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Elliptic

/-- Matrix of an endomorphism with the Hessian's order of its two indices. -/
def operatorCoordinateMatrix {n s : ℕ} :
    (CoordinateSpace n s →L[ℝ] CoordinateSpace n s) →ₗ[ℝ]
      Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ where
  toFun H i j := inner ℝ (H (coordinateVector i)) (coordinateVector j)
  map_add' H K := by
    ext i j
    change inner ℝ ((H + K) (coordinateVector i)) (coordinateVector j) =
      inner ℝ (H (coordinateVector i)) (coordinateVector j) +
        inner ℝ (K (coordinateVector i)) (coordinateVector j)
    simp only [add_apply, inner_add_left]
  map_smul' c H := by
    ext i j
    change inner ℝ ((c • H) (coordinateVector i)) (coordinateVector j) =
      c * inner ℝ (H (coordinateVector i)) (coordinateVector j)
    simp only [smul_apply, inner_smul_left, starRingEnd_apply, star_trivial]

theorem operatorCoordinateMatrix_fderiv_gradient {n s : ℕ}
    {f : CoordinateSpace n s → ℝ} (hf : ContDiff ℝ 2 f) (x : CoordinateSpace n s) :
    operatorCoordinateMatrix (fderiv ℝ (gradient f) x) = realHessian f x := by
  ext i j
  exact OAI.Analysis.PDE.Elliptic.inner_fderiv_gradient hf x (coordinateVector i) (coordinateVector j)

theorem operatorCoordinateMatrix_rankOne {n s : ℕ} (v : CoordinateSpace n s) :
    operatorCoordinateMatrix (rankOne ℝ v v) = fun i j ↦ v i * v j := by
  ext i j
  change inner ℝ (rankOne ℝ v v (coordinateVector i)) (coordinateVector j) = v i * v j
  simp [rankOne_apply, coordinateVector,
    EuclideanSpace.inner_single_right]

def logOperatorFunctional {n : ℕ} (A : Matrix (Fin n) (Fin n) Q) :
    (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4) →ₗ[ℝ] ℝ :=
  (OAI.LinearAlgebra.Moore.mooreDet n A)⁻¹ • (OAI.LinearAlgebra.Moore.mooreDifferentialLinear n A).comp
    ((hessianMatrixLinear OAI.Analysis.Calculus.Quaternion.fourSlots).comp operatorCoordinateMatrix)

theorem logOperatorFunctional_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (H : CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4) :
    logOperatorFunctional A H =
      OAI.LinearAlgebra.Moore.mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (operatorCoordinateMatrix H)) /
        OAI.LinearAlgebra.Moore.mooreDet n A := by
  change (OAI.LinearAlgebra.Moore.mooreDet n A)⁻¹ *
    OAI.LinearAlgebra.Moore.mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (operatorCoordinateMatrix H)) = _
  ring

/-- The actual symmetric real coefficient operator of log det H. -/
def logRealOperator {n : ℕ} (A : Matrix (Fin n) (Fin n) Q) :
    CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 :=
  OAI.Analysis.PDE.Elliptic.symmetricTraceDual (EuclideanSpace.basisFun (Fin n × Fin 4) ℝ)
    (logOperatorFunctional A)

theorem logRealOperator_isSymmetric {n : ℕ} (A : Matrix (Fin n) (Fin n) Q) :
    (logRealOperator A).toLinearMap.IsSymmetric :=
  OAI.Analysis.PDE.Elliptic.symmetricTraceDual_isSymmetric _ _

theorem logRealOperator_symbol {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (v : CoordinateSpace n 4) :
    inner ℝ v (logRealOperator A v) = logPrincipalSymbol A v := by
  rw [logRealOperator, OAI.Analysis.PDE.Elliptic.symmetricTraceDual_symbol, logOperatorFunctional_apply,
    operatorCoordinateMatrix_rankOne, OAI.Analysis.Calculus.Quaternion.hessianMap_rankOne]
  rfl

theorem logRealOperator_linearization {n : ℕ}
    (A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) Q)
    {f : CoordinateSpace n 4 → ℝ} (hf : ContDiff ℝ 2 f) (x : CoordinateSpace n 4) :
    OAI.Analysis.PDE.Elliptic.ellipticTrace (fun y ↦ logRealOperator (A y)) f x =
      mooreLinearization A f x / OAI.LinearAlgebra.Moore.mooreDet n (A x) := by
  change OAI.Analysis.PDE.Elliptic.traceRight (fderiv ℝ (gradient f) x)
    (OAI.Analysis.PDE.Elliptic.symmetricTraceDual _ (logOperatorFunctional (A x))) = _
  rw [OAI.Analysis.PDE.Elliptic.symmetricTraceDual_represents _ _ _ (OAI.Analysis.PDE.Elliptic.fderiv_gradient_isSymmetric hf x),
    logOperatorFunctional_apply, operatorCoordinateMatrix_fderiv_gradient hf]
  rfl

end OAI.Analysis.PDE.Dirichlet
