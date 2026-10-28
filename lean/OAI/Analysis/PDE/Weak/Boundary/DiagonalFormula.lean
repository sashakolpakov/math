import OAI.Analysis.PDE.Weak.Boundary.NormalFormula

/-! The missing diagonal Hessian derivative is recovered from the actual
divergence equation and the tangential derivatives of the H¹ gradient. -/

noncomputable section
open Set Filter _root_.MeasureTheory
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

open OAI.Analysis.PDE.Variational

variable {m : ℕ}

theorem H1Zero.normal_diagonal_formula
    {Ω Ω₀ : Set (OAI.Analysis.PDE.Variational.CellCoordinates m)} (hΩ : IsOpen Ω) {p : H1Pair m}
    (hp : p ∈ H1Zero Ω₀) (k : Fin (m + 1))
    (a : Fin (m + 1) → Fin (m + 1) → OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    {M D lam : ℝ} (hlam : 0 < lam)
    (hM : ∀ i j x, ‖a i j x‖ ≤ M)
    (hD : ∀ i j l x, ‖fderiv ℝ (a i j) x (Pi.single l 1)‖ ≤ D)
    (hpos : ∀ x, lam ≤ a k k x)
    (H : OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m) (hH : MemLp H 2 volume)
    (hcoef : ∀ x i, H x i = ∑ j, a i j x * p.2 x j)
    (f : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ) (hf : MemLp f 2 volume)
    (hweak : WeakDivergenceEquation Ω H f)
    (g : Fin (m + 1) → OAI.Analysis.PDE.Variational.CellCoordinates m → OAI.Analysis.PDE.Variational.CellVectors m)
    (hg : ∀ i, MemLp (g i) 2 volume)
    (hd : ∀ i, i ≠ k → HasWeakDirectionalDerivativeOn volume Ω (Pi.single i 1) p.2 (g i)) :
    let G := fun x =>
      (-f x -
        ∑ i ∈ Finset.univ.erase k, ∑ j,
          (a i j x * g i x j + fderiv ℝ (a i j) x (Pi.single i 1) * p.2 x j) -
        ∑ j ∈ Finset.univ.erase k,
          (a k j x * g j x k + fderiv ℝ (a k j) x (Pi.single k 1) * p.2 x j) -
        fderiv ℝ (a k k) x (Pi.single k 1) * p.2 x k) / a k k x
    MemLp G 2 volume ∧
      HasWeakDirectionalDerivativeOn volume Ω (Pi.single k 1) (fun x => p.2 x k) G := by
  have hU (j) : MemLp (fun x => p.2 x j) 2 volume := memLp_cell_component (Lp.memLp p.2) j
  have hG (i j) : MemLp (fun x => g i x j) 2 volume := memLp_cell_component (hg i) j
  have hDa (i j l) : Continuous (fun x => fderiv ℝ (a i j) x (Pi.single l 1)) :=
    (((ha i j).of_le (by simp) : ContDiff ℝ 1 (a i j)).continuous_fderiv one_ne_zero).clm_apply
      continuous_const
  have hprod (i j) : MemLp (fun x => a i j x * p.2 x j) 2 volume :=
    memLp_bounded_scalar_mul volume (ha i j).continuous (hU j) (hM i j)
  let t : Fin (m + 1) → OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ := fun i x =>
    ∑ j, (a i j x * g i x j + fderiv ℝ (a i j) x (Pi.single i 1) * p.2 x j)
  have ht (i) : MemLp (t i) 2 volume := by
    apply memLp_finsetSum
    intro j _
    exact (memLp_bounded_scalar_mul volume (ha i j).continuous (hG i j) (hM i j)).add
      (memLp_bounded_scalar_mul volume (hDa i j i) (hU j) (hD i j i))
  have hpartial (i) (hi : i ≠ k) :
      HasWeakDirectionalDerivativeOn volume Ω (Pi.single i 1) (fun x => H x i) (t i) := by
    have hh := OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.scalar_finset_sum volume Finset.univ
      (fun j x => a i j x * p.2 x j)
      (fun j x => a i j x * g i x j + fderiv ℝ (a i j) x (Pi.single i 1) * p.2 x j)
      (fun j _ => hprod i j)
      (fun j _ => (memLp_bounded_scalar_mul volume (ha i j).continuous (hG i j) (hM i j)).add
        (memLp_bounded_scalar_mul volume (hDa i j i) (hU j) (hD i j i)))
      (fun j _ => ((hd i hi).scalar_component j).scalar_mul volume (a i j)
        ((ha i j).of_le (by simp)) (hU j) (hG i j))
    apply hh.congr_on volume
    · filter_upwards with x
      intro _
      exact (hcoef x i).symm
    · filter_upwards with x
      intro _
      rfl
  let K : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ := fun x => ∑ j ∈ Finset.univ.erase k, a k j x * p.2 x j
  let V : OAI.Analysis.PDE.Variational.CellCoordinates m → ℝ := fun x => ∑ j ∈ Finset.univ.erase k,
    (a k j x * g j x k + fderiv ℝ (a k j) x (Pi.single k 1) * p.2 x j)
  have hK : MemLp K 2 volume := memLp_finsetSum _ (fun j _ => hprod k j)
  have hV : MemLp V 2 volume := memLp_finsetSum _ (fun j _ =>
    (memLp_bounded_scalar_mul volume (ha k j).continuous (hG j k) (hM k j)).add
      (memLp_bounded_scalar_mul volume (hDa k j k) (hU j) (hD k j k)))
  have hDK : HasWeakDirectionalDerivativeOn volume Ω (Pi.single k 1) K V := by
    apply OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.scalar_finset_sum volume (Finset.univ.erase k)
    · intro j _
      exact hprod k j
    · intro j _
      exact (memLp_bounded_scalar_mul volume (ha k j).continuous (hG j k) (hM k j)).add
        (memLp_bounded_scalar_mul volume (hDa k j k) (hU j) (hD k j k))
    · intro j hj
      exact (OAI.Analysis.PDE.Weak.H1Zero.mixed_weak_derivative hΩ hp j k (g j) (hg j)
        (hd j (Finset.mem_erase.mp hj).1)).scalar_mul volume (a k j)
          ((ha k j).of_le (by simp)) (hU j) (hG j k)
  apply normal_recovery_formula hΩ hweak hH hf k t ht hpartial
    (a k k) (fun x => p.2 x k) K V (ha k k)
    (fun x => ne_of_gt (hlam.trans_le (hpos x))) (hU k) hK hV hDK
  · intro x
    rw [hcoef]
    exact (Finset.sum_erase_add Finset.univ (fun j => a k j x * p.2 x j)
      (Finset.mem_univ k)).symm.trans (add_comm _ _)
  · exact hD k k k
  · intro x
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hlam.trans_le (hpos x)))]
    exact inv_anti₀ hlam (hpos x)

end OAI.Analysis.PDE.Weak
