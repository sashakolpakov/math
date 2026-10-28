import OAI.Analysis.Calculus.Current.Physical.Background
import OAI.Analysis.Calculus.Current.Physical.Compact
import OAI.Analysis.PDE.Concentration.BarrierDeterminant

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Matrix OAI.Analysis.Calculus.Current OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore
open scoped MatrixOrder ComplexOrder Matrix.Norms.Elementwise

theorem quaternion_norm_sum_le {ι : Type*} [Fintype ι] (v : ι → Quaternion ℝ) :
    (star v ⬝ᵥ v).re ≤ (Fintype.card ι : ℝ) * ‖v‖ ^ 2 := by
  have he : (star v ⬝ᵥ v).re = ∑ i, ‖v i‖ ^ 2 := by
    simp only [dotProduct, OAI.LinearAlgebra.Moore.quaternion_re_sum, Pi.star_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [Quaternion.star_mul_self, Quaternion.re_coe, Quaternion.normSq_eq_norm_mul_self]
    ring
  rw [he]
  calc
    _ ≤ ∑ _i : ι, ‖v‖ ^ 2 := Finset.sum_le_sum fun i _ =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2
    _ = _ := by simp

theorem complexify_shift_of_sup_norm_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] (A : Matrix ι ι (Quaternion ℝ)) (hA : A.IsHermitian) {c : ℝ} (hc : 0 ≤ c)
    (hb : ∀ v : ι → Quaternion ℝ, c * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ (A *ᵥ v)).re) :
    (OAI.LinearAlgebra.Moore.complexify (A - (c / Fintype.card ι) • 1)).PosSemidef := by
  have hH : (A - (c / Fintype.card ι) • 1).IsHermitian := by
    change (A - (c / Fintype.card ι) • 1)ᴴ = _
    simp [Matrix.conjTranspose_sub, hA.eq, OAI.LinearAlgebra.Moore.quaternionMatrix_conjTranspose_real_smul]
  apply (OAI.Analysis.Calculus.Quaternion.indexed_complexify_posSemidef_iff _ hH).mpr
  intro v
  have hcard : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hq := mul_le_mul_of_nonneg_left (quaternion_norm_sum_le v)
    (show 0 ≤ c / Fintype.card ι by positivity)
  have he : c / (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) * ‖v‖ ^ 2) = c * ‖v‖ ^ 2 := by
    field_simp
  rw [he] at hq
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_smul,
    Quaternion.re_sub, Quaternion.re_smul]
  change 0 ≤ (star v ⬝ᵥ (A *ᵥ v)).re - c / Fintype.card ι * (star v ⬝ᵥ v).re
  linarith [hb v]

/-- Genuine uniform matrix coercivity of the physical defining Hessian. The
power of `a` comes from the actual rational fiber geometry. -/
theorem physical_defining_matrix_lower (d : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : ℝ) (τ : ℂ) (q : Option (Fin d) → ℂ),
      0 < a → a ≤ ‖τ‖ → ‖τ‖ ≤ 4 * a → OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q ≤ 0 →
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.Calculus.Current.physicalFiberHessian (1 / 10) a τ q - (c / a ^ 2) • 1)).PosSemidef := by
  obtain ⟨c, hc, hb⟩ := OAI.Analysis.Calculus.Current.physicalFiberHessian_small_time_lower d
  refine ⟨c / (d + 1), by positivity, ?_⟩
  intro a τ q ha ht ht' hr
  have hy := (OAI.Analysis.Calculus.Current.fiber_collar_height_bounds a (OAI.Analysis.Calculus.Current.physicalEmbedding τ q) ha
    (by simpa only [OAI.Analysis.Calculus.Current.imaginaryTime_physicalEmbedding] using ht) (hr.trans (by norm_num))).1
  have hY : OAI.Analysis.Calculus.Current.physicalEmbedding τ q none ≠ 0 := norm_ne_zero_iff.mp (ha.trans_le hy).ne'
  have hH : (OAI.Analysis.Calculus.Current.physicalFiberHessian (1 / 10) a τ q).IsHermitian := by
    rw [OAI.Analysis.Calculus.Current.physicalFiberHessian_factorization _ _ _ _ hY]
    change ((4 : ℝ) • _)ᴴ = _
    simp [Matrix.conjTranspose_mul]
  have h := complexify_shift_of_sup_norm_lower _ hH
    (show 0 ≤ c / a ^ 2 by positivity) (hb a τ q ha ht ht' hr)
  convert h using 1 ; simp only [Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one] ;
    congr 3 ; ring

theorem physical_background_outer {d : ℕ} (τ : ℂ) (q : Option (Fin d) → ℂ)
    (hY : OAI.Analysis.Calculus.Current.physicalEmbedding τ q none ≠ 0) :
    OAI.Analysis.Calculus.Current.physicalBackgroundHessian τ q = OAI.Analysis.Calculus.Quaternion.outer (fun b =>
      (2 : ℝ) • OAI.Analysis.Calculus.Current.complexK (star (OAI.Analysis.Calculus.Current.physicalPhaseRow (OAI.Analysis.Calculus.Current.physicalEmbedding τ q) b))) := by
  have he : (fun p : (Option (Fin d) → ℂ) => OAI.Analysis.Calculus.Current.fiberMap 1 10 (OAI.Analysis.Calculus.Current.physicalEmbedding τ p) none) =
      (fun p => OAI.Analysis.Calculus.Current.phi (OAI.Analysis.Calculus.Current.physicalEmbedding τ p)) := by funext p; simp [OAI.Analysis.Calculus.Current.fiberMap]
  have hf : ContDiffAt ℂ 2 (fun p => OAI.Analysis.Calculus.Current.phi (OAI.Analysis.Calculus.Current.physicalEmbedding τ p)) q := by
    rw [← he]
    exact (OAI.Analysis.Calculus.Current.contDiffAt_fiberMap_complex 1 10 (OAI.Analysis.Calculus.Current.physicalEmbedding τ q) hY none).comp q
      (OAI.Analysis.Calculus.Current.contDiff_physicalEmbedding_complex τ).contDiffAt
  apply Matrix.ext
  intro i j
  simp only [OAI.Analysis.Calculus.Current.physicalBackgroundHessian, OAI.Analysis.Calculus.Quaternion.imaginaryHessian_norm_sq hf,
    OAI.Analysis.Calculus.Current.fderiv_physicalPhi_single τ q hY, OAI.Analysis.Calculus.Quaternion.outer, ← OAI.Analysis.Calculus.Current.complexK_star,
    map_mul, smul_mul_assoc]
  ext <;> simp <;> ring

end OAI.Analysis.PDE.Concentration
