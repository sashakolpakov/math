import OAI.Analysis.PDE.Dirichlet.RealOperator
import OAI.LinearAlgebra.Moore.Smooth
import OAI.Analysis.PDE.Dirichlet.C2HolderPositive
import OAI.Analysis.PDE.Dirichlet.ComparisonLocal

open Set Filter InnerProductSpace
open scoped Topology Matrix.Norms.Elementwise MatrixOrder ComplexOrder ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Elliptic OAI.Analysis.Normed.Function.Holder

def detOperatorFunctional {n : ℕ} (A : Matrix (Fin n) (Fin n) Q) :
    (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4) →ₗ[ℝ] ℝ :=
  (OAI.LinearAlgebra.Moore.mooreDifferentialLinear n A).comp
    ((hessianMatrixLinear OAI.Analysis.Calculus.Quaternion.fourSlots).comp operatorCoordinateMatrix)

/-- Polynomial real coefficient operator of the determinant equation,
defined and smooth even away from the positive cone. -/
def detRealOperator {n : ℕ} (A : Matrix (Fin n) (Fin n) Q) :
    CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 :=
  OAI.Analysis.PDE.Elliptic.symmetricTraceDual (EuclideanSpace.basisFun (Fin n × Fin 4) ℝ)
    (detOperatorFunctional A)

theorem detRealOperator_isSymmetric {n : ℕ} (A : Matrix (Fin n) (Fin n) Q) :
    (detRealOperator A).toLinearMap.IsSymmetric := OAI.Analysis.PDE.Elliptic.symmetricTraceDual_isSymmetric _ _

theorem contDiff_detRealOperator (n : ℕ) (k : ℕ∞ω) :
    ContDiff ℝ k (detRealOperator (n := n)) := by
  unfold detRealOperator OAI.Analysis.PDE.Elliptic.symmetricTraceDual
  apply ContDiff.sum
  intro j _
  apply ContDiff.sum
  intro i _
  change ContDiff ℝ k (fun A : Matrix (Fin n) (Fin n) Q ↦
    (OAI.LinearAlgebra.Moore.mooreDifferential n A
      (OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (operatorCoordinateMatrix
        (rankOne ℝ ((EuclideanSpace.basisFun (Fin n × Fin 4) ℝ) i)
          ((EuclideanSpace.basisFun (Fin n × Fin 4) ℝ) j)))) / 2) • _)
  exact ((OAI.LinearAlgebra.Moore.contDiff_mooreDifferential_left n k _).div_const 2).smul contDiff_const

theorem detRealOperator_symbol {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (v : CoordinateSpace n 4) :
    inner ℝ v (detRealOperator A v) =
      OAI.LinearAlgebra.Moore.mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.outer (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots v)) := by
  rw [detRealOperator, OAI.Analysis.PDE.Elliptic.symmetricTraceDual_symbol]
  change OAI.LinearAlgebra.Moore.mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots
    (operatorCoordinateMatrix (rankOne ℝ v v))) = _
  rw [operatorCoordinateMatrix_rankOne, OAI.Analysis.Calculus.Quaternion.hessianMap_rankOne]

theorem detRealOperator_symbol_eq_log {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef) (v : CoordinateSpace n 4) :
    inner ℝ v (detRealOperator A v) = OAI.LinearAlgebra.Moore.mooreDet n A * logPrincipalSymbol A v := by
  rw [detRealOperator_symbol, logPrincipalSymbol]
  exact (mul_div_cancel₀ _ (OAI.LinearAlgebra.Moore.mooreDet_pos_of_complexify_posDef A hA).ne').symm

/-- The determinant linearization inherits quantitative uniform ellipticity
from the logarithmic linearization and two-sided density bounds. -/
theorem detRealOperator_elliptic_bounds {n : ℕ}
    (A : Matrix (Fin n) (Fin n) Q) (hA : (OAI.LinearAlgebra.Moore.complexify A).PosDef)
    {a B lam L : ℝ} (_ : 0 ≤ a) (hlam : 0 ≤ lam) (hL : 0 ≤ L)
    (hdet : a ≤ OAI.LinearAlgebra.Moore.mooreDet n A ∧ OAI.LinearAlgebra.Moore.mooreDet n A ≤ B)
    (hell : ∀ v : CoordinateSpace n 4,
      lam * ‖v‖ ^ 2 ≤ logPrincipalSymbol A v ∧ logPrincipalSymbol A v ≤ L * ‖v‖ ^ 2)
    (v : CoordinateSpace n 4) :
    (a * lam) * ‖v‖ ^ 2 ≤ inner ℝ v (detRealOperator A v) ∧
      inner ℝ v (detRealOperator A v) ≤ (B * L) * ‖v‖ ^ 2 := by
  rw [detRealOperator_symbol_eq_log A hA]
  have hp : 0 ≤ OAI.LinearAlgebra.Moore.mooreDet n A := (OAI.LinearAlgebra.Moore.mooreDet_pos_of_complexify_posDef A hA).le
  constructor
  · calc
      (a * lam) * ‖v‖ ^ 2 = a * (lam * ‖v‖ ^ 2) := by ring
      _ ≤ OAI.LinearAlgebra.Moore.mooreDet n A * logPrincipalSymbol A v :=
        mul_le_mul hdet.1 (hell v).1 (mul_nonneg hlam (sq_nonneg _)) hp
  · calc
      OAI.LinearAlgebra.Moore.mooreDet n A * logPrincipalSymbol A v ≤ OAI.LinearAlgebra.Moore.mooreDet n A * (L * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hell v).2 hp
      _ ≤ B * (L * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hdet.2 (mul_nonneg hL (sq_nonneg _))
      _ = (B * L) * ‖v‖ ^ 2 := by ring

theorem detRealOperator_linearization {n : ℕ}
    (A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) Q)
    {f : CoordinateSpace n 4 → ℝ} (hf : ContDiff ℝ 2 f) (x : CoordinateSpace n 4) :
    OAI.Analysis.PDE.Elliptic.ellipticTrace (fun y ↦ detRealOperator (A y)) f x = mooreLinearization A f x := by
  change OAI.Analysis.PDE.Elliptic.traceRight (fderiv ℝ (gradient f) x)
    (OAI.Analysis.PDE.Elliptic.symmetricTraceDual _ (detOperatorFunctional (A x))) = _
  rw [OAI.Analysis.PDE.Elliptic.symmetricTraceDual_represents _ _ _ (OAI.Analysis.PDE.Elliptic.fderiv_gradient_isSymmetric hf x)]
  change OAI.LinearAlgebra.Moore.mooreDifferential n (A x)
    (OAI.Analysis.Calculus.Quaternion.hessianMap OAI.Analysis.Calculus.Quaternion.fourSlots (operatorCoordinateMatrix (fderiv ℝ (gradient f) x))) = _
  rw [operatorCoordinateMatrix_fderiv_gradient hf]
  rfl

theorem detRealOperator_linearization_at {n : ℕ}
    (A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) Q)
    {f : CoordinateSpace n 4 → ℝ} {x : CoordinateSpace n 4}
    (hf : ContDiffAt ℝ 2 f x) :
    OAI.Analysis.PDE.Elliptic.ellipticTrace (fun y ↦ detRealOperator (A y)) f x = mooreLinearization A f x := by
  obtain ⟨g, hg, heq⟩ := exists_contDiff_extension_near_point hf
  have hgrad : gradient g =ᶠ[𝓝 x] gradient f := by
    filter_upwards [heq.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun L ↦ (toDual ℝ (CoordinateSpace n 4)).symm L) hy
  have hD := hgrad.fderiv_eq (𝕜 := ℝ)
  have hH := quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.fourSlots heq
  have h := detRealOperator_linearization A hg x
  unfold OAI.Analysis.PDE.Elliptic.ellipticTrace at h ⊢
  unfold mooreLinearization at h ⊢
  rw [hD, hH] at h
  exact h

/-- The Banach derivative is the genuine real elliptic operator, including
for functions that are only C² inside the domain. -/
theorem fderiv_mooreDirichletOperator_ellipticTrace {n : ℕ}
    {Ω K : Set (CoordinateSpace n 4)} {hΩK : Ω ⊆ K} {α : ℝ}
    (hΩ : IsOpen Ω) (hα : 0 ≤ α) (f w : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    {x : CoordinateSpace n 4} (hx : x ∈ Ω) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (fderiv ℝ (mooreDirichletOperator hα OAI.Analysis.Calculus.Quaternion.fourSlots) f w) ⟨x, hΩK hx⟩ =
      OAI.Analysis.PDE.Elliptic.ellipticTrace (fun y ↦ detRealOperator
        (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value f)) y))
        (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value w)) x := by
  rw [fderiv_mooreDirichletOperator_value hΩ hα OAI.Analysis.Calculus.Quaternion.fourSlots f w hx]
  exact (detRealOperator_linearization_at _
    ((OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_value hΩ w).contDiffAt (hΩ.mem_nhds hx))).symm

end OAI.Analysis.PDE.Dirichlet
