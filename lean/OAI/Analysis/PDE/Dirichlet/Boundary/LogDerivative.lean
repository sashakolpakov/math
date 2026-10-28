import OAI.Analysis.Normed.Function.Holder.Boundary.LogCoefficient
import OAI.Analysis.PDE.Elliptic.Boundary.LocalExtension

/-! The derivative of the logarithmic coefficient has a uniform Hölder
bound on bounded uniformly positive families. A genuine smooth extension
from a compact subset of the positive-determinant locus is constructed,
so no global regularity at singular matrices is assumed. -/

noncomputable section
open Set Metric
open scoped Matrix.Norms.Elementwise ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Elliptic OAI.Analysis.Normed.Function.Holder

local instance logDerivativeEndGroup (n : ℕ) :
    NormedAddCommGroup (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4) := inferInstance
local instance logDerivativeEndSpace (n : ℕ) :
    NormedSpace ℝ (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4) := inferInstance
local instance logDerivativeMatrixGroup (n : ℕ) :
    NormedAddCommGroup (Matrix (Fin n) (Fin n) Q) :=
  inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → Q))
local instance logDerivativeMatrixSpace (n : ℕ) :
    NormedSpace ℝ (Matrix (Fin n) (Fin n) Q) :=
  inferInstanceAs (NormedSpace ℝ (Fin n → Fin n → Q))
local instance logDerivativeMapGroup (n : ℕ) :
    NormedAddCommGroup (Matrix (Fin n) (Fin n) Q →L[ℝ]
      (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4)) :=
  inferInstanceAs (NormedAddCommGroup ((Fin n → Fin n → Q) →L[ℝ]
    (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4)))
local instance logDerivativeMapSpace (n : ℕ) :
    NormedSpace ℝ (Matrix (Fin n) (Fin n) Q →L[ℝ]
      (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4)) :=
  inferInstanceAs (NormedSpace ℝ ((Fin n → Fin n → Q) →L[ℝ]
    (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4)))

theorem contDiffAt_logRealOperator (n : ℕ) (k : ℕ∞ω)
    (A : Matrix (Fin n) (Fin n) Q) (hA : OAI.LinearAlgebra.Moore.mooreDet n A ≠ 0) :
    ContDiffAt ℝ k (logRealOperator (n := n)) A := by
  have he : logRealOperator (n := n) = fun B => (OAI.LinearAlgebra.Moore.mooreDet n B)⁻¹ • detRealOperator B :=
    funext logRealOperator_eq_smul_detRealOperator
  rw [he]
  exact ((OAI.LinearAlgebra.Moore.contDiff_mooreDet n k).contDiffAt.inv hA).smul
    (contDiff_detRealOperator n k).contDiffAt

theorem exists_logRealDerivative_holder_bound {X : Type*} [MetricSpace X]
    (n : ℕ) {α R μ : ℝ} (hα : 0 ≤ α) (hR : 0 ≤ R) (hμ : 0 < μ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ A : OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix (Fin n) (Fin n) Q) α, ‖A‖ ≤ R →
      (∀ x, μ ≤ OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x)) →
      ∃ B : OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix (Fin n) (Fin n) Q →L[ℝ]
          (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4)) α,
        (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = fderiv ℝ (logRealOperator (n := n)) (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x)) ∧
        ‖B‖ ≤ C * (1 + ‖A‖) := by
  let K : Set (Matrix (Fin n) (Fin n) Q) := closedBall 0 R ∩ {B | μ ≤ OAI.LinearAlgebra.Moore.mooreDet n B}
  have hK : IsCompact K := (isCompact_closedBall _ _).inter_right
    (isClosed_le continuous_const (OAI.LinearAlgebra.Moore.contDiff_mooreDet n 1).continuous)
  obtain ⟨g, hg, hgeq⟩ := OAI.Analysis.PDE.Elliptic.exists_contDiff_extension_near_compact
    (f := logRealOperator (n := n)) (k := 2) hK
    (fun A hA => contDiffAt_logRealOperator n 2 A (hμ.trans_le hA.2).ne')
  obtain ⟨C, hC, hcompose⟩ := OAI.Analysis.Normed.Function.Holder.HolderMap.exists_compose_contDiff_bound (X := X)
    (hg.fderiv_right (m := 1) (by norm_num)) hα hR
  refine ⟨C, hC, ?_⟩
  intro A hA hdet
  obtain ⟨B, hB, hBn⟩ := hcompose A hA
  refine ⟨B, ?_, hBn⟩
  intro x
  refine (hB x).trans ?_
  apply (hgeq _ ?_).fderiv_eq
  refine ⟨?_, hdet x⟩
  simpa only [mem_closedBall, dist_zero_right] using (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le A x).trans hA

/-- The actual spatial derivative of the coefficient is Hölder whenever
the Hessian and its spatial derivative are Hölder.  This is the C¹,α
coefficient input for the second boundary Schauder pass. -/
theorem exists_logRealOperator_directional_holder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) {S : Set E} {α R μ : ℝ}
    (hα : 0 ≤ α) (hR : 0 ≤ R) (hμ : 0 < μ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ A V : OAI.Analysis.Normed.Function.Holder.HolderMap S (Matrix (Fin n) (Fin n) Q) α, ‖A‖ ≤ R →
      ∀ a : E → Matrix (Fin n) (Fin n) Q, ∀ v : E,
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = a x) →
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ a x v) →
      (∀ x : S, DifferentiableAt ℝ a x) →
      (∀ x : S, μ ≤ OAI.LinearAlgebra.Moore.mooreDet n (a x)) →
      ∃ B : OAI.Analysis.Normed.Function.Holder.HolderMap S (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4) α,
        (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value B x =
          fderiv ℝ (fun y => logRealOperator (a y)) x v) ∧
        ‖B‖ ≤ C * (1+‖A‖) * ‖V‖ := by
  obtain ⟨C, hC, hc⟩ := exists_logRealDerivative_holder_bound (X := S) n hα hR hμ
  refine ⟨2*C, by positivity, ?_⟩
  intro A V hA a v heA heV ha hdet
  obtain ⟨D, heD, hD⟩ := hc A hA (fun x => by rw [heA]; exact hdet x)
  refine ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.action hα D V, ?_, ?_⟩
  · intro x
    have hl : DifferentiableAt ℝ (logRealOperator (n := n)) (a x) :=
      (contDiffAt_logRealOperator n 1 (a x) (hμ.trans_le (hdet x)).ne').differentiableAt one_ne_zero
    have hd := fderiv_comp (x : E) hl (ha x)
    have hDx := (heD x).trans (congrArg (fderiv ℝ (logRealOperator (n := n))) (heA x))
    have he := congrArg₂
      (fun (L : Matrix (Fin n) (Fin n) Q →L[ℝ]
        (CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4)) (q : Matrix (Fin n) (Fin n) Q) => L q)
      hDx (heV x)
    exact he.trans (congrArg (fun L => L v) hd).symm
  · apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα D V).trans
    calc
      _ ≤ 2*(C*(1+‖A‖))*‖V‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hD (by norm_num)) (norm_nonneg _)
      _ = _ := by ring

end OAI.Analysis.PDE.Dirichlet
