import OAI.LinearAlgebra.Moore.Outer
import OAI.LinearAlgebra.Moore.Smooth

/-! The rank-one differential identity of the Moore cofactor, the algebraic
null-Lagrangian input to cofactor divergence. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open Matrix OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet
open scoped Matrix.Norms.Elementwise MatrixOrder ComplexOrder

def outerVariation {n : ℕ} (v w : Fin n → Quaternion ℝ) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) :=
  vecMulVec w (star v) + vecMulVec v (star w)

theorem outerVariation_isHermitian {n : ℕ} (v w : Fin n → Quaternion ℝ) :
    (outerVariation v w).IsHermitian := by
  change (outerVariation v w)ᴴ = outerVariation v w
  simp only [outerVariation, Matrix.conjTranspose_add, Matrix.conjTranspose_vecMulVec,
    star_star, add_comm]

theorem hasDerivAt_outer {n : ℕ} (v w : Fin n → Quaternion ℝ) :
    HasDerivAt (fun s : ℝ ↦ OAI.Analysis.Calculus.Quaternion.outer (v + s • w)) (outerVariation v w) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  have hi : HasDerivAt (fun s : ℝ ↦ v i + s • w i) (w i) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const (w i)).const_add (v i) using 1
    simp
  have hj : HasDerivAt (fun s : ℝ ↦ v j + s • w j) (w j) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const (w j)).const_add (v j) using 1
    simp
  have hstar := quaternionStarCLM.hasFDerivAt.comp_hasDerivAt 0 hj
  change HasDerivAt (fun s : ℝ ↦ star (v j + s • w j)) (star (w j)) 0 at hstar
  have hprod := hi.mul hstar
  change HasDerivAt (fun s : ℝ ↦ (v i + s • w i) * star (v j + s • w j))
    (w i * star (v j + 0 • w j) + (v i + 0 • w i) * star (w j)) 0 at hprod
  simpa only [OAI.Analysis.Calculus.Quaternion.outer, outerVariation, Matrix.add_apply, vecMulVec_apply, Pi.star_apply,
    zero_smul, add_zero, Pi.add_apply, Pi.smul_apply] using hprod

def mooreDifferentialCLM (n : ℕ) (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) →L[ℝ] ℝ :=
  (mooreDifferentialLinear n A).toContinuousLinearMap

theorem mooreDifferential_outerVariation_update {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (v w : Fin n → Quaternion ℝ) (t : ℝ) :
    mooreDifferential n (A + t • OAI.Analysis.Calculus.Quaternion.outer v) (outerVariation v w) =
      mooreDifferential n A (outerVariation v w) := by
  by_cases ht : t = 0
  · simp [ht]
  have hL : HasDerivAt (fun s : ℝ ↦ mooreDet n (A + t • OAI.Analysis.Calculus.Quaternion.outer (v + s • w)))
      (mooreDifferential n (A + t • OAI.Analysis.Calculus.Quaternion.outer v) (t • outerVariation v w)) 0 := by
    let F : ℝ → Matrix (Fin n) (Fin n) (Quaternion ℝ) := fun s ↦ A + t • OAI.Analysis.Calculus.Quaternion.outer (v + s • w)
    have hentry (i j : Fin n) : HasDerivAt (fun s ↦ F s i j) ((t • outerVariation v w) i j) 0 := by
      have ho := hasDerivAt_pi.mp (hasDerivAt_pi.mp (hasDerivAt_outer v w) i) j
      change HasDerivAt (fun s ↦ A i j + t • OAI.Analysis.Calculus.Quaternion.outer (v + s • w) i j)
        (t • outerVariation v w i j) 0
      exact (ho.const_smul t).const_add (A i j)
    simpa only [F, zero_smul, add_zero] using
      hasDerivAt_mooreDet_path n F (t • outerVariation v w) 0 hentry
  have hR := (((mooreDifferentialCLM n A).hasFDerivAt.comp_hasDerivAt 0
    (hasDerivAt_outer v w)).const_mul t).const_add (mooreDet n A)
  change HasDerivAt (fun s : ℝ ↦ mooreDet n A + t * mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.outer (v + s • w)))
    (t * mooreDifferential n A (outerVariation v w)) 0 at hR
  have heq : (fun s : ℝ ↦ mooreDet n (A + t • OAI.Analysis.Calculus.Quaternion.outer (v + s • w))) =
      (fun s : ℝ ↦ mooreDet n A + t * mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.outer (v + s • w))) := by
    funext s
    exact mooreDet_add_outer_differential A (v + s • w) t
  rw [heq] at hL
  have he := hL.unique hR
  rw [mooreDifferential_smul] at he
  exact mul_left_cancel₀ ht he

theorem realTrace_mul_vecMulVec {n : ℕ}
    (C : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (v w : Fin n → Quaternion ℝ) :
    realTrace (C * vecMulVec v (star w)) = (star w ⬝ᵥ C *ᵥ v).re := by
  rw [Matrix.mul_vecMulVec]
  change (∑ i, (C *ᵥ v) i * star (w i)).re = (∑ i, star (w i) * (C *ᵥ v) i).re
  simp only [quaternion_re_sum]
  exact Finset.sum_congr rfl (fun i _ ↦ quaternion_re_mul_comm _ _)

theorem hermitian_dotProduct_real_swap {n : ℕ}
    (C : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hC : C.IsHermitian)
    (v w : Fin n → Quaternion ℝ) :
    (star v ⬝ᵥ C *ᵥ w).re = (star w ⬝ᵥ C *ᵥ v).re := by
  have hCe : Cᴴ = C := hC
  have hs : star (star w ⬝ᵥ C *ᵥ v) = star v ⬝ᵥ C *ᵥ w := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_dotProduct_star, Matrix.star_vecMul,
      star_star, hCe]
  rw [← hs]
  simp

theorem realTrace_mul_outerVariation {n : ℕ}
    (C : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hC : C.IsHermitian)
    (v w : Fin n → Quaternion ℝ) :
    realTrace (C * outerVariation v w) = 2 * (star w ⬝ᵥ C *ᵥ v).re := by
  rw [outerVariation, Matrix.mul_add, realTrace_add, realTrace_mul_vecMulVec,
    realTrace_mul_vecMulVec, hermitian_dotProduct_real_swap C hC v w]
  ring

/-- A rank-one cofactor update annihilates the updating vector exactly, before
taking any derivative. This includes singular and indefinite backgrounds. -/
theorem mooreCofactor_outer_mulVec {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (v : Fin n → Quaternion ℝ) (t : ℝ) :
    mooreCofactor n (A + t • OAI.Analysis.Calculus.Quaternion.outer v) *ᵥ v = mooreCofactor n A *ᵥ v := by
  let C := mooreCofactor n (A + t • OAI.Analysis.Calculus.Quaternion.outer v) - mooreCofactor n A
  have hC : C.IsHermitian :=
    (mooreCofactor_isHermitian n _).sub (mooreCofactor_isHermitian n _)
  have hzero (w : Fin n → Quaternion ℝ) : 2 * (star w ⬝ᵥ C *ᵥ v).re = 0 := by
    rw [← realTrace_mul_outerVariation C hC v w]
    dsimp only [C]
    rw [Matrix.sub_mul, realTrace_sub,
      mooreCofactor_pairing n _ _ (outerVariation_isHermitian v w),
      mooreCofactor_pairing n _ _ (outerVariation_isHermitian v w),
      mooreDifferential_outerVariation_update, sub_self]
  have hz : C *ᵥ v = 0 := by
    by_contra hn
    have hI : (complexify (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ))).PosDef := by
      rw [complexify_one]
      exact Matrix.PosDef.one
    have hp := (complexify_posDef_iff isHermitian_one).mp hI (C *ᵥ v) hn
    rw [quaternionForm_eq_dotProduct, Matrix.one_mulVec] at hp
    linarith [hzero (C *ᵥ v)]
  exact sub_eq_zero.mp (by simpa only [C, Matrix.sub_mulVec] using hz)

theorem mooreCofactor_outer_vecMul {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (v : Fin n → Quaternion ℝ) (t : ℝ) :
    star v ᵥ* mooreCofactor n (A + t • OAI.Analysis.Calculus.Quaternion.outer v) = star v ᵥ* mooreCofactor n A := by
  have h := congrArg star (mooreCofactor_outer_mulVec A v t)
  have hC₀ : (mooreCofactor n A)ᴴ = mooreCofactor n A := mooreCofactor_isHermitian n A
  have hC₁ : (mooreCofactor n (A + t • OAI.Analysis.Calculus.Quaternion.outer v))ᴴ = mooreCofactor n (A + t • OAI.Analysis.Calculus.Quaternion.outer v) :=
    mooreCofactor_isHermitian n _
  simpa only [Matrix.star_mulVec, hC₀, hC₁] using h

def fixedVecMulLinear {n : ℕ} (v : Fin n → Quaternion ℝ) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) →ₗ[ℝ] (Fin n → Quaternion ℝ) where
  toFun A := v ᵥ* A
  map_add' A B := by
    funext j
    simp [Matrix.vecMul, dotProduct, mul_add, Finset.sum_add_distrib]
  map_smul' c A := by
    funext j
    simp [Matrix.vecMul, dotProduct, Finset.smul_sum]

def fixedVecMulCLM {n : ℕ} (v : Fin n → Quaternion ℝ) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) →L[ℝ] (Fin n → Quaternion ℝ) :=
  (fixedVecMulLinear v).toContinuousLinearMap

/-- The cofactor's actual Fréchet differential satisfies the rank-one
annihilation identity in the left orientation of quaternionic divergence. -/
theorem mooreCofactor_fderiv_outer_vecMul {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (v : Fin n → Quaternion ℝ) :
    star v ᵥ* (fderiv ℝ (mooreCofactor n) A (OAI.Analysis.Calculus.Quaternion.outer v)) = 0 := by
  have hcurve : HasDerivAt (fun s : ℝ ↦ A + s • OAI.Analysis.Calculus.Quaternion.outer v) (OAI.Analysis.Calculus.Quaternion.outer v) 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const (OAI.Analysis.Calculus.Quaternion.outer v)).const_add A using 1
    simp
  have hC := ((contDiff_mooreCofactor n 1).differentiable (by simp)) A
  have hC' : HasFDerivAt (mooreCofactor n) (fderiv ℝ (mooreCofactor n) A)
      (A + (0 : ℝ) • OAI.Analysis.Calculus.Quaternion.outer v) := by
    simpa only [zero_smul, add_zero] using! hC.hasFDerivAt
  have hd : HasDerivAt (fun s : ℝ ↦ mooreCofactor n (A + s • OAI.Analysis.Calculus.Quaternion.outer v))
      (fderiv ℝ (mooreCofactor n) A (OAI.Analysis.Calculus.Quaternion.outer v)) 0 := by
    simpa only [zero_smul, add_zero, Function.comp_def] using!
      hC'.comp_hasDerivAt 0 hcurve
  have hl := (fixedVecMulCLM (star v)).hasFDerivAt.comp_hasDerivAt 0 hd
  change HasDerivAt (fun s : ℝ ↦ star v ᵥ* mooreCofactor n (A + s • OAI.Analysis.Calculus.Quaternion.outer v))
    (star v ᵥ* (fderiv ℝ (mooreCofactor n) A (OAI.Analysis.Calculus.Quaternion.outer v))) 0 at hl
  have hc : HasDerivAt (fun s : ℝ ↦ star v ᵥ* mooreCofactor n (A + s • OAI.Analysis.Calculus.Quaternion.outer v)) 0 0 := by
    simpa only [mooreCofactor_outer_vecMul] using
      hasDerivAt_const (0 : ℝ) (star v ᵥ* mooreCofactor n A)
  exact hl.unique hc

end OAI.LinearAlgebra.Moore
