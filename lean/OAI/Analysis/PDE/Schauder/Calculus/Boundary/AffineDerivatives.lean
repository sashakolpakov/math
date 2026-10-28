import OAI.Analysis.PDE.Schauder.Calculus.Boundary.KernelIntegral

/-! Exact derivative scaling under an invertible scalar affine map. -/

noncomputable section
open Set
namespace OAI.Analysis.PDE.Schauder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_affine_scalar (f : E → F) {t : ℝ} (ht : t ≠ 0)
    (z x : E) (n : ℕ) :
    iteratedFDeriv ℝ n (fun y => f (t • y + z)) x =
      t ^ n • iteratedFDeriv ℝ n f (t • x + z) := by
  let L : E ≃L[ℝ] E := ContinuousLinearEquiv.equivOfInverse
    (t • ContinuousLinearMap.id ℝ E) (t⁻¹ • ContinuousLinearMap.id ℝ E)
    (fun y => by simp [smul_smul, ht]) (fun y => by simp [smul_smul, ht])
  have hi := L.iteratedFDerivWithin_comp_right (fun y => f (y + z))
    uniqueDiffOn_univ (mem_univ (L x)) n
  simp only [preimage_univ, iteratedFDerivWithin_univ] at hi
  change iteratedFDeriv ℝ n ((fun y => f (y + z)) ∘ L) x = _
  rw [hi, iteratedFDeriv_comp_add_right]
  ext v
  change iteratedFDeriv ℝ n f (t • x + z) (fun i => t • v i) =
    (t ^ n) • iteratedFDeriv ℝ n f (t • x + z) v
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ n f (t • x + z)).map_smul_univ (fun _ => t) v

theorem norm_iteratedFDeriv_affine_scalar (f : E → F) {t : ℝ} (ht : t ≠ 0)
    (z x : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => f (t • y + z)) x‖ =
      |t| ^ n * ‖iteratedFDeriv ℝ n f (t • x + z)‖ := by
  rw [iteratedFDeriv_affine_scalar f ht z x n, norm_smul, Real.norm_eq_abs, abs_pow]

theorem norm_iteratedFDeriv_sub_const (f : E → F) (c : F) (x : E) {n : ℕ} (hn : n ≠ 0) :
    ‖iteratedFDeriv ℝ n (fun y => f y - c) x‖ = ‖iteratedFDeriv ℝ n f x‖ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [← norm_iteratedFDeriv_fderiv, ← norm_iteratedFDeriv_fderiv]
  congr 2
  funext y
  exact fderiv_sub_const c

end OAI.Analysis.PDE.Schauder
