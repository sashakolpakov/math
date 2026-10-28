import OAI.Analysis.Calculus.Quaternion.CofactorDivergence
import OAI.LinearAlgebra.Moore.Adjugate
import OAI.LinearAlgebra.Moore.Kernel
import OAI.LinearAlgebra.Moore.Corank
import OAI.LinearAlgebra.Moore.PositiveInverse

/-! The actual Moore cofactor on an arbitrary finite coordinate index set. -/

noncomputable section
namespace OAI.Analysis.Calculus.Quaternion

open OAI.LinearAlgebra.Moore
open scoped Matrix Matrix.Norms.Elementwise ComplexOrder ContDiff

variable {ι : Type*} [Fintype ι]

def matrixToFin (A : Matrix ι ι Q) : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) Q :=
  fun i j => A ((Fintype.equivFin ι).symm i) ((Fintype.equivFin ι).symm j)

def matrixFromFin (A : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) Q) : Matrix ι ι Q :=
  fun i j => A (Fintype.equivFin ι i) (Fintype.equivFin ι j)

def vectorToFin (v : ι → Q) : Fin (Fintype.card ι) → Q :=
  fun i => v ((Fintype.equivFin ι).symm i)

def vectorFromFin (v : Fin (Fintype.card ι) → Q) : ι → Q :=
  fun i => v (Fintype.equivFin ι i)

theorem vectorToFin_fromFin (v : Fin (Fintype.card ι) → Q) :
    vectorToFin (vectorFromFin (ι := ι) v) = v := by
  funext i
  simp [vectorToFin, vectorFromFin]

def matrixToFinCLM : Matrix ι ι Q →L[ℝ]
    Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) Q :=
  ({ toFun := matrixToFin
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : Matrix ι ι Q →ₗ[ℝ] _).toContinuousLinearMap

def matrixFromFinCLM : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) Q →L[ℝ]
    Matrix ι ι Q :=
  ({ toFun := matrixFromFin
     map_add' := fun _ _ => rfl
     map_smul' := fun _ _ => rfl } : _ →ₗ[ℝ] Matrix ι ι Q).toContinuousLinearMap

theorem matrixToFin_fromFin (A : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) Q) :
    matrixToFin (matrixFromFin (ι := ι) A) = A := by
  apply Matrix.ext
  intro i j
  simp [matrixToFin, matrixFromFin]

theorem vectorToFin_injective : Function.Injective (vectorToFin (ι := ι)) := by
  intro u v h
  funext i
  simpa [vectorToFin] using congrFun h (Fintype.equivFin ι i)

theorem matrixToFin_mulVec (A : Matrix ι ι Q) (v : ι → Q) :
    matrixToFin A *ᵥ vectorToFin v = vectorToFin (A *ᵥ v) := by
  funext i
  simp only [matrixToFin, vectorToFin, Matrix.mulVec, dotProduct]
  exact (Fintype.equivFin ι).symm.sum_comp
    (fun j => A ((Fintype.equivFin ι).symm i) j * v j)

theorem star_vecMul_matrixFromFin (v : ι → Q)
    (A : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) Q) :
    star v ᵥ* matrixFromFin A =
      fun b => (star (vectorToFin v) ᵥ* A) (Fintype.equivFin ι b) := by
  funext b
  simp only [Matrix.vecMul, dotProduct, Pi.star_apply, matrixFromFin, vectorToFin]
  simpa only [Equiv.symm_apply_apply] using (Fintype.equivFin ι).sum_comp
    (fun i => star (v ((Fintype.equivFin ι).symm i)) * A i (Fintype.equivFin ι b))

theorem quaternionForm_matrixToFin (A : Matrix ι ι Q) (v : ι → Q) :
    OAI.Analysis.PDE.Dirichlet.quaternionForm (matrixToFin A) (vectorToFin v) =
      star v ⬝ᵥ (A *ᵥ v) := by
  rw [OAI.LinearAlgebra.Moore.quaternionForm_eq_dotProduct, matrixToFin_mulVec]
  exact (Fintype.equivFin ι).symm.sum_comp
    (fun i => star (v i) * (A *ᵥ v) i)

theorem complexify_matrixToFin_posSemidef (A : Matrix ι ι Q)
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosSemidef) : (OAI.LinearAlgebra.Moore.complexify (matrixToFin A)).PosSemidef :=
  hA.submatrix (fun i : Fin (Fintype.card ι) × Fin 2 =>
    ((Fintype.equivFin ι).symm i.1, i.2))

theorem indexed_complexify_posSemidef_iff (A : Matrix ι ι Q) (hA : A.IsHermitian) :
    (OAI.LinearAlgebra.Moore.complexify A).PosSemidef ↔ ∀ v, 0 ≤ (star v ⬝ᵥ (A *ᵥ v)).re := by
  constructor
  · intro h v
    have hh := (OAI.LinearAlgebra.Moore.complexify_posSemidef_iff
      (hA.submatrix (Fintype.equivFin ι).symm)).mp
        (complexify_matrixToFin_posSemidef A h) (vectorToFin v)
    change 0 ≤ (OAI.Analysis.PDE.Dirichlet.quaternionForm (matrixToFin A) (vectorToFin v)).re at hh
    simpa only [quaternionForm_matrixToFin] using hh
  · intro h
    have hh : (OAI.LinearAlgebra.Moore.complexify (matrixToFin A)).PosSemidef := by
      apply (OAI.LinearAlgebra.Moore.complexify_posSemidef_iff (hA.submatrix (Fintype.equivFin ι).symm)).mpr
      intro v
      have hv := h (vectorFromFin v)
      rw [← quaternionForm_matrixToFin, vectorToFin_fromFin] at hv
      exact hv
    have hback := hh.submatrix (fun i : ι × Fin 2 => (Fintype.equivFin ι i.1, i.2))
    simpa only [Matrix.submatrix, OAI.LinearAlgebra.Moore.complexify, matrixToFin, Equiv.symm_apply_apply] using! hback

def indexedMooreDet (A : Matrix ι ι Q) : ℝ := OAI.LinearAlgebra.Moore.mooreDet (Fintype.card ι) (matrixToFin A)

def indexedCofactor (A : Matrix ι ι Q) : Matrix ι ι Q :=
  matrixFromFin (OAI.LinearAlgebra.Moore.mooreCofactor (Fintype.card ι) (matrixToFin A))

theorem indexedCofactor_isHermitian (A : Matrix ι ι Q) : (indexedCofactor A).IsHermitian := by
  exact (OAI.LinearAlgebra.Moore.mooreCofactor_isHermitian (Fintype.card ι) (matrixToFin A)).submatrix
    (Fintype.equivFin ι)

theorem indexedCofactor_posSemidef (A : Matrix ι ι Q) (hA : (OAI.LinearAlgebra.Moore.complexify A).PosSemidef) :
    (OAI.LinearAlgebra.Moore.complexify (indexedCofactor A)).PosSemidef := by
  have hFin : (OAI.LinearAlgebra.Moore.complexify (matrixToFin A)).PosSemidef :=
    hA.submatrix (fun i : Fin (Fintype.card ι) × Fin 2 =>
      ((Fintype.equivFin ι).symm i.1, i.2))
  exact (OAI.LinearAlgebra.Moore.mooreCofactor_posSemidef _ hFin).submatrix
    (fun i : ι × Fin 2 => (Fintype.equivFin ι i.1, i.2))

theorem contDiff_indexedCofactor (k : ℕ∞ω) : ContDiff ℝ k (indexedCofactor (ι := ι)) := by
  change ContDiff ℝ k ((matrixFromFinCLM (ι := ι)) ∘
    (OAI.LinearAlgebra.Moore.mooreCofactor (Fintype.card ι)) ∘ (matrixToFinCLM (ι := ι)))
  exact (matrixFromFinCLM (ι := ι)).contDiff.comp
    ((OAI.LinearAlgebra.Moore.contDiff_mooreCofactor (Fintype.card ι) k).comp (matrixToFinCLM (ι := ι)).contDiff)

theorem hasFDerivAt_indexedCofactor (A : Matrix ι ι Q) :
    HasFDerivAt indexedCofactor
      (matrixFromFinCLM.comp
        ((fderiv ℝ (OAI.LinearAlgebra.Moore.mooreCofactor (Fintype.card ι)) (matrixToFin A)).comp matrixToFinCLM)) A := by
  have hC := ((OAI.LinearAlgebra.Moore.contDiff_mooreCofactor (Fintype.card ι) 1).differentiable (by simp))
    (matrixToFin A)
  simpa only using! matrixFromFinCLM.hasFDerivAt.comp A
    (hC.hasFDerivAt.comp A matrixToFinCLM.hasFDerivAt)

theorem fderiv_indexedCofactor (A B : Matrix ι ι Q) :
    fderiv ℝ indexedCofactor A B =
      matrixFromFin (fderiv ℝ (OAI.LinearAlgebra.Moore.mooreCofactor (Fintype.card ι)) (matrixToFin A) (matrixToFin B)) := by
  have hF : fderiv ℝ indexedCofactor A = matrixFromFinCLM.comp
      ((fderiv ℝ (OAI.LinearAlgebra.Moore.mooreCofactor (Fintype.card ι)) (matrixToFin A)).comp matrixToFinCLM) := by
    simpa only using! (hasFDerivAt_indexedCofactor A).fderiv
  rw [hF]
  rfl

theorem indexedCofactor_fderiv_outer_vecMul (A : Matrix ι ι Q) (v : ι → Q) :
    star v ᵥ* fderiv ℝ indexedCofactor A (outer v) = 0 := by
  rw [fderiv_indexedCofactor, star_vecMul_matrixFromFin]
  have hout : matrixToFin (outer v) = outer (vectorToFin v) := rfl
  rw [hout, OAI.LinearAlgebra.Moore.mooreCofactor_fderiv_outer_vecMul]
  rfl

theorem indexedCofactor_directionalHessian_divergence
    [DecidableEq ι]
    {E s : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype s] [DecidableEq s] (e : s → Q) (d : ι × s → E)
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 3 f x) (b : ι) :
    strongDivergence e
      (fun p => fderiv ℝ (fun y => indexedCofactor (directionalHessian e d f y)) x (d p)) b = 0 := by
  apply directionalHessian_conservation e d hf indexedCofactor
  · exact (contDiff_indexedCofactor 1).differentiable (by simp) _
  · intro v
    exact indexedCofactor_fderiv_outer_vecMul _ v

theorem indexedMooreDet_zero_of_kernel (A : Matrix ι ι Q) (hA : A.IsHermitian)
    (v : ι → Q) (hv : v ≠ 0) (hAv : A *ᵥ v = 0) : indexedMooreDet A = 0 := by
  apply OAI.LinearAlgebra.Moore.mooreDet_zero_of_kernel (Fintype.card ι) (matrixToFin A)
    (hA.submatrix (Fintype.equivFin ι).symm) (vectorToFin v)
  · rw [matrixToFin_mulVec, hAv]
    rfl
  · intro hz
    apply hv
    apply vectorToFin_injective
    change vectorToFin v = 0
    exact hz

theorem indexedCofactor_image_in_kernel (A : Matrix ι ι Q) (hA : A.IsHermitian)
    (hdet : indexedMooreDet A = 0) (v : ι → Q) :
    A *ᵥ (indexedCofactor A *ᵥ v) = 0 := by
  apply vectorToFin_injective
  rw [← matrixToFin_mulVec, ← matrixToFin_mulVec]
  rw [indexedCofactor, matrixToFin_fromFin]
  exact OAI.LinearAlgebra.Moore.mooreCofactor_image_in_kernel (matrixToFin A)
    (hA.submatrix (Fintype.equivFin ι).symm) hdet (vectorToFin v)

theorem indexedCofactor_diag_pos (A : Matrix ι ι Q) (k : ι)
    (hA : (OAI.LinearAlgebra.Moore.complexify A).PosSemidef) (hdet : indexedMooreDet A = 0)
    (hT : ∀ v ≠ 0, v k = 0 → 0 < (star v ⬝ᵥ (A *ᵥ v)).re) :
    0 < (indexedCofactor A k k).re := by
  apply OAI.LinearAlgebra.Moore.mooreCofactor_diag_pos_of_tangential_pos (matrixToFin A) (Fintype.equivFin ι k)
    (complexify_matrixToFin_posSemidef A hA) hdet
  intro v hv hvk
  have hne : vectorFromFin (ι := ι) v ≠ 0 := by
    intro hz
    apply hv
    rw [← vectorToFin_fromFin v, hz]
    rfl
  have ht := hT (vectorFromFin v) hne hvk
  rw [← quaternionForm_matrixToFin, vectorToFin_fromFin] at ht
  exact ht

end OAI.Analysis.Calculus.Quaternion
