import OAI.Analysis.Calculus.SmoothExtension.HalfspaceCoefficients
import OAI.Analysis.Calculus.FiniteExtension.Halfspace.Extension.Map
import Mathlib.Analysis.Calculus.SmoothSeries

/-! The countable reflection operator and summable bounds for every jet. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace OAI.Analysis.Calculus.SmoothExtension

open OAI.Analysis.Calculus.FiniteExtension

abbrev ReflectionIndex := Σ n : ℕ, Fin (n+1)

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def seeleyReflection (ℓ : E →L[ℝ] ℝ) (ν : E) (f : E → F) (x : E) : F :=
  ∑' i : ReflectionIndex, seeleyWeight i • f (OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i) x)

theorem reflectionLinear_norm_le (ℓ : E →L[ℝ] ℝ) (ν : E) (i : ReflectionIndex) :
    ‖OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i)‖ ≤
      (‖ContinuousLinearMap.id ℝ E - ℓ.smulRight ν‖ + ‖ℓ.smulRight ν‖) * |seeleyNode i| := by
  have hi : 1 ≤ |seeleyNode i| := by
    rw [abs_of_nonpos ((seeleyNode_le_neg_one i).trans (by norm_num))]
    linarith [seeleyNode_le_neg_one i]
  calc
    _ ≤ ‖ContinuousLinearMap.id ℝ E - ℓ.smulRight ν‖ +
      ‖seeleyNode i • ℓ.smulRight ν‖ := norm_add_le _ _
    _ = ‖ContinuousLinearMap.id ℝ E - ℓ.smulRight ν‖ +
      |seeleyNode i| * ‖ℓ.smulRight ν‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ ≤ _ := by nlinarith [norm_nonneg (ContinuousLinearMap.id ℝ E - ℓ.smulRight ν)]

theorem seeley_jet_summable (ℓ : E →L[ℝ] ℝ) (ν : E) (q : ℕ)
    (A : ReflectionIndex → ContinuousMultilinearMap ℝ (fun _ : Fin q => E) F)
    (B : ℝ) (hB : 0 ≤ B) (hA : ∀ i, ‖A i‖ ≤ B) :
    Summable (fun i => seeleyWeight i • (A i).compContinuousLinearMap
      (fun _ => OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i))) := by
  let C := ‖ContinuousLinearMap.id ℝ E - ℓ.smulRight ν‖ + ‖ℓ.smulRight ν‖
  have hC : 0 ≤ C := add_nonneg (norm_nonneg _) (norm_nonneg _)
  apply Summable.of_norm_bounded ((seeley_abs_moment_summable q).mul_left (B*C^q))
  intro i
  rw [norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |seeleyWeight i| * (‖A i‖ * ‖OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i)‖^q) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa using (A i).norm_compContinuousLinearMap_le
        (fun _ : Fin q => OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i))
    _ ≤ |seeleyWeight i| * (B * (C * |seeleyNode i|)^q) := by
      gcongr
      · exact hA i
      · exact reflectionLinear_norm_le ℓ ν i
    _ = _ := by rw [mul_pow]; ring

omit [CompleteSpace F] in
theorem seeley_multilinear_moments {q : ℕ}
    (A : MultilinearMap ℝ (fun _ : Fin q => E) F) (t v : Fin q → E) :
    (∑' i : ReflectionIndex, seeleyWeight i •
      A (fun j => t j + seeleyNode i • v j)) = A (fun j => t j + v j) := by
  classical
  have hexpand (a : ℝ) : A (fun i => t i + a • v i) =
      ∑ s : Finset (Fin q), a ^ s.card • A (s.piecewise v t) := by
    have he : (fun i => t i + a • v i) = (fun i => a • v i) + t := by
      funext i
      simp only [Pi.add_apply, add_comm]
    rw [he,A.map_add_univ]
    apply Finset.sum_congr rfl
    intro s _
    exact OAI.Analysis.Calculus.FiniteExtension.multilinear_piecewise_smul A t v s a
  simp_rw [hexpand,Finset.smul_sum,smul_smul]
  rw [Summable.tsum_finsetSum]
  · simp_rw [(seeley_moment_summable _).tsum_smul_const, seeley_moment, one_smul]
    have he : (fun i => t i+v i) = v+t := by funext i; simp [add_comm]
    rw [he,A.map_add_univ]
  · intro s _
    exact (seeley_moment_summable s.card).smul_const _

theorem seeley_jet_moments {q : ℕ} (ℓ : E →L[ℝ] ℝ) (ν : E)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) F) :
    (∑' i : ReflectionIndex, seeleyWeight i • A.compContinuousLinearMap
      (fun _ => OAI.Analysis.Calculus.FiniteExtension.reflectionLinear ℓ ν (seeleyNode i))) = A := by
  ext v
  rw [ContinuousMultilinearMap.tsum_eval
    (seeley_jet_summable ℓ ν q (fun _ => A) ‖A‖ (norm_nonneg _) (fun _ => le_rfl))]
  simp only [smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,OAI.Analysis.Calculus.FiniteExtension.reflectionLinear_apply]
  have h := seeley_multilinear_moments A.toMultilinearMap
    (fun i => v i - ℓ (v i) • ν) (fun i => ℓ (v i) • ν)
  have heval (w : Fin q → E) : A.toMultilinearMap w = A w := rfl
  simpa only [heval,sub_add_cancel] using h

end OAI.Analysis.Calculus.SmoothExtension
