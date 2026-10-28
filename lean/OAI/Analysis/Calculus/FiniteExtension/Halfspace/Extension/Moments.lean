import OAI.Analysis.Normed.Function.Sobolev.Reflection.Coefficients

/-! The reflection moments match arbitrary multilinear jets, not only
pure normal derivatives. -/

noncomputable section
open Set
open scoped BigOperators
namespace OAI.Analysis.Calculus.FiniteExtension

open OAI.Analysis.Normed.Function.Sobolev

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem multilinear_piecewise_smul {q : ℕ}
    (A : MultilinearMap ℝ (fun _ : Fin q => E) F)
    (t v : Fin q → E) (s : Finset (Fin q)) (a : ℝ) :
    A (s.piecewise (fun i => a • v i) t) = a ^ s.card • A (s.piecewise v t) := by
  classical
  have he : s.piecewise (fun i => a • v i) t =
      s.piecewise (fun i => a • s.piecewise v t i) (s.piecewise v t) := by
    funext i
    by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
  rw [he, A.map_piecewise_smul]
  simp

theorem reflection_multilinear_moments {N q : ℕ} (hq : q < N)
    (A : MultilinearMap ℝ (fun _ : Fin q => E) F) (t v : Fin q → E) :
    (∑ j : Fin N, OAI.Analysis.Normed.Function.Sobolev.reflectionCoefficient N j •
      A (fun i => t i + OAI.Analysis.Normed.Function.Sobolev.reflectionNode j • v i)) = A (fun i => t i + v i) := by
  classical
  have hexpand (a : ℝ) : A (fun i => t i + a • v i) =
      ∑ s : Finset (Fin q), a ^ s.card • A (s.piecewise v t) := by
    have he : (fun i => t i + a • v i) = (fun i => a • v i) + t := by
      funext i
      simp only [Pi.add_apply, add_comm]
    rw [he, A.map_add_univ]
    apply Finset.sum_congr rfl
    intro s _
    exact multilinear_piecewise_smul A t v s a
  simp_rw [hexpand, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hm (s : Finset (Fin q)) :
      (∑ j : Fin N, OAI.Analysis.Normed.Function.Sobolev.reflectionCoefficient N j * OAI.Analysis.Normed.Function.Sobolev.reflectionNode j ^ s.card) = 1 := by
    apply OAI.Analysis.Normed.Function.Sobolev.reflectionCoefficient_moment
    have hcard : s.card ≤ q := by simpa using s.card_le_univ
    omega
  simp_rw [← Finset.sum_smul, hm, one_smul]
  have he : (fun i => t i + v i) = v + t := by funext i; simp only [Pi.add_apply, add_comm]
  rw [he, A.map_add_univ]

theorem reflection_continuousMultilinear_moments {N q : ℕ} (hq : q < N)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin q => E) F)
    (T R : E →L[ℝ] E) (hTR : T + R = ContinuousLinearMap.id ℝ E) :
    (∑ j : Fin N, OAI.Analysis.Normed.Function.Sobolev.reflectionCoefficient N j •
      A.compContinuousLinearMap (fun _ => T + OAI.Analysis.Normed.Function.Sobolev.reflectionNode j • R)) = A := by
  classical
  ext v
  simp only [sum_apply, smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change (∑ j : Fin N, OAI.Analysis.Normed.Function.Sobolev.reflectionCoefficient N j •
    A (fun i => T (v i) + OAI.Analysis.Normed.Function.Sobolev.reflectionNode j • R (v i))) = A v
  calc
    _ = A (fun i => T (v i) + R (v i)) :=
      reflection_multilinear_moments hq A.toMultilinearMap (fun i => T (v i)) (fun i => R (v i))
    _ = A v := by
      congr 1
      funext i
      exact congrArg (fun L : E →L[ℝ] E => L (v i)) hTR

end OAI.Analysis.Calculus.FiniteExtension
