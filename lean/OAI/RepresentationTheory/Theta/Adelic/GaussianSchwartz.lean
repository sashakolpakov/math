import OAI.RepresentationTheory.Weil.AdelicSplitting.RealCharacters

/-! # Gaussian Schwartz -/

namespace OAI.RepresentationTheory.Theta.Adelic.GaussianSchwartz

noncomputable section

/-! A concrete real Gaussian in the actual Schwartz--Bruhat space. -/

open scoped ContDiff

open OAI.RepresentationTheory.Weil.AdelicSplitting.RealCharacters.LocalAnalysis

theorem complex_exp_derivative_norm (n : ℕ) (z : ℂ) :
    ‖iteratedFDeriv ℝ n Complex.exp z‖ = Real.exp z.re := by
  have h := (Complex.contDiff_exp (𝕜 := ℂ) (n := n)).contDiffAt.restrictScalars_iteratedFDeriv
    (𝕜 := ℝ) (x := z)
  rw [← h]
  change ‖(iteratedFDeriv ℂ n Complex.exp z).restrictScalars ℝ‖ = _
  rw [ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hi : iteratedDeriv n Complex.exp = Complex.exp := by
    simpa only [one_mul, one_pow] using iteratedDeriv_cexp_const_mul n 1
  rw [hi, Complex.norm_exp]

theorem polynomial_gaussian_bound (M : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (1 + t) ^ M * Real.exp (-t ^ 2) ≤ 2 ^ M * (M.factorial : ℝ) * Real.exp 1 := by
  have hs : 0 ≤ 1 + t ^ 2 := by positivity
  have hfactor := Real.pow_div_factorial_le_exp (1 + t ^ 2) hs M
  have hpow : (1 + t ^ 2) ^ M ≤ Real.exp (1 + t ^ 2) * (M.factorial : ℝ) :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < M.factorial)).mp hfactor
  have hp : (1 + t) ^ M ≤ (2 * (1 + t ^ 2)) ^ M := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [sq_nonneg (t - 1)]
  calc
    _ ≤ (2 * (1 + t ^ 2)) ^ M * Real.exp (-t ^ 2) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = 2 ^ M * ((1 + t ^ 2) ^ M * Real.exp (-t ^ 2)) := by rw [mul_pow]; ring
    _ ≤ 2 ^ M * ((Real.exp (1 + t ^ 2) * M.factorial) * Real.exp (-t ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le) (by positivity)
    _ = 2 ^ M * (M.factorial : ℝ) * Real.exp 1 := by
      have he : Real.exp (1 + t ^ 2) * Real.exp (-t ^ 2) = Real.exp 1 := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ = (2 ^ M * M.factorial) * (Real.exp (1 + t ^ 2) * Real.exp (-t ^ 2)) := by ring
        _ = _ := by rw [he]

def gaussianOfExponent {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : V → ℂ) (hQ : Function.HasTemperateGrowth Q)
    (hRe : ∀ x, (Q x).re = -‖x‖ ^ 2) : SchwartzMap V ℂ where
  toFun x := Complex.exp (Q x)
  smooth' := Complex.contDiff_exp.comp hQ.1
  decay' k n := by
    obtain ⟨l, C, hC, hbound⟩ := hQ.norm_iteratedFDeriv_le_uniform n
    let A : ℝ := n.factorial * (1 + C) ^ n
    let M : ℕ := k + l * n
    refine ⟨A * (2 ^ M * (M.factorial : ℝ) * Real.exp 1), ?_⟩
    intro x
    have hD : ∀ i, 1 ≤ i → i ≤ n →
        ‖iteratedFDeriv ℝ i Q x‖ ≤ ((1 + C) * (1 + ‖x‖) ^ l) ^ i := by
      intro i hi hin
      calc
        _ ≤ C * (1 + ‖x‖) ^ l := hbound i hin x
        _ ≤ (1 + C) * (1 + ‖x‖) ^ l := by gcongr; linarith
        _ ≤ _ := le_self_pow₀
          (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by simp))) (by omega)
    have hExp : ∀ i, i ≤ n → ‖iteratedFDeriv ℝ i Complex.exp (Q x)‖ ≤ Real.exp (-‖x‖ ^ 2) := by
      intro i _
      rw [complex_exp_derivative_norm, hRe]
    have hderiv := norm_iteratedFDeriv_comp_le
      (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)) hQ.1 (mod_cast le_top) x hExp hD
    have hA : 0 ≤ A := by dsimp [A]; positivity
    calc
      _ ≤ ‖x‖ ^ k * (n.factorial * Real.exp (-‖x‖ ^ 2) * ((1 + C) * (1 + ‖x‖) ^ l) ^ n) :=
        mul_le_mul_of_nonneg_left hderiv (by positivity)
      _ ≤ (1 + ‖x‖) ^ k *
          (n.factorial * Real.exp (-‖x‖ ^ 2) * ((1 + C) * (1 + ‖x‖) ^ l) ^ n) := by
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (norm_nonneg x) (by linarith : ‖x‖ ≤ 1 + ‖x‖) k) (by positivity)
      _ = A * ((1 + ‖x‖) ^ M * Real.exp (-‖x‖ ^ 2)) := by
        dsimp [A, M]
        rw [mul_pow, ← pow_mul, pow_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (polynomial_gaussian_bound M ‖x‖ (norm_nonneg x)) hA

def gaussianOne : Weil.Local.FunctionsMetaplectic.Construction.schwartzBruhat ℝ 1 := by
  let Q : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ 1 → ℂ := fun x => -((x 0 : ℂ) ^ 2)
  have hQ : Function.HasTemperateGrowth Q :=
    (((Complex.ofRealCLM.comp (ContinuousLinearMap.proj 0 : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ 1 →L[ℝ] ℝ)).hasTemperateGrowth).pow 2).neg
  have hRe : ∀ x, (Q x).re = -‖x‖ ^ 2 := by
    intro x
    have hx : x = fun _ : Fin 1 => x 0 := funext fun i => congrArg x (Subsingleton.elim i 0)
    rw [hx]
    simp [Q, ← Complex.ofReal_pow, Real.norm_eq_abs, sq_abs]
  exact Weil.AdelicSplitting.RealCharacters.LocalAnalysis.realSchwartzToBruhat (gaussianOfExponent Q hQ hRe)

theorem gaussianOne_apply (x : Weil.Local.FunctionsMetaplectic.Construction.Position ℝ 1) :
    gaussianOne.val x = Complex.exp (-((x 0 : ℂ) ^ 2)) := rfl

theorem gaussianOne_zero : gaussianOne.val 0 = 1 := by simp [gaussianOne_apply]

end

end OAI.RepresentationTheory.Theta.Adelic.GaussianSchwartz
