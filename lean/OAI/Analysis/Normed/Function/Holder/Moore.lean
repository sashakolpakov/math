import OAI.Analysis.Normed.Function.Holder.Banach.Polynomial
import OAI.LinearAlgebra.Moore.Derivative
import Mathlib.Analysis.Matrix.Normed

open scoped Matrix.Norms.Elementwise ContDiff
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

open OAI.LinearAlgebra.Moore

def quaternionEntryCLM (n : ℕ) (i j : Fin n) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) →L[ℝ] Quaternion ℝ where
  toFun A := A i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := (show (Matrix (Fin n) (Fin n) (Quaternion ℝ) →ₗ[ℝ] Quaternion ℝ) from
    { toFun := fun A ↦ A i j, map_add' := fun _ _ ↦ rfl,
      map_smul' := fun _ _ ↦ rfl }).continuous_of_finiteDimensional

def skewEntryCLM (n : ℕ) (i j : Fin n × Fin 2) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) →L[ℝ] ℂ :=
  (OAI.LinearAlgebra.Moore.skewQuaternionEntryCLM i.2 j.2).comp (quaternionEntryCLM n i.1 j.1)

variable {X : Type*} [MetricSpace X] {α : ℝ}

/-- The exact Pfaffian formula of the source, evaluated in the Hölder space. -/
def pfaffianField (hα : 0 ≤ α) (n : ℕ)
    (A : HolderMap X (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α) : HolderMap X ℂ α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.map (ContinuousLinearMap.mul ℝ ℂ ((2 ^ n * (n.factorial : ℂ))⁻¹))
    (∑ σ : Equiv.Perm (Fin n × Fin 2),
      OAI.Analysis.Normed.Function.Holder.HolderMap.map (ContinuousLinearMap.mul ℝ ℂ (((Equiv.Perm.sign σ : ℤ) : ℂ)))
        (OAI.Analysis.Normed.Function.Holder.HolderMap.finiteProduct hα Finset.univ (fun i : Fin n ↦
          OAI.Analysis.Normed.Function.Holder.HolderMap.map (skewEntryCLM n (σ (i, 0)) (σ (i, 1))) A)))

@[simp] theorem value_pfaffianField (hα : 0 ≤ α) (n : ℕ)
    (A : HolderMap X (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α) (x : X) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (pfaffianField hα n A) x = OAI.LinearAlgebra.Moore.pfaffian n (OAI.LinearAlgebra.Moore.skewComplexify (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x)) := by
  simp only [pfaffianField, OAI.Analysis.Normed.Function.Holder.HolderMap.value_map, OAI.Analysis.Normed.Function.Holder.HolderMap.value_sum,
    OAI.Analysis.Normed.Function.Holder.HolderMap.value_finiteProduct, ContinuousLinearMap.mul_apply', OAI.LinearAlgebra.Moore.pfaffian]
  rfl

theorem contDiff_pfaffianField (hα : 0 ≤ α) (n : ℕ) (k : ℕ∞ω) :
    ContDiff ℝ k (pfaffianField (X := X) hα n) := by
  unfold pfaffianField
  apply (OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (ContinuousLinearMap.mul ℝ ℂ ((2 ^ n * (n.factorial : ℂ))⁻¹))).contDiff.comp
  apply ContDiff.sum
  intro σ hσ
  apply (OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (ContinuousLinearMap.mul ℝ ℂ (((Equiv.Perm.sign σ : ℤ) : ℂ)))).contDiff.comp
  exact OAI.Analysis.Normed.Function.Holder.HolderMap.contDiff_finiteProduct hα Finset.univ k (fun i ↦
    (OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM (skewEntryCLM n (σ (i, 0)) (σ (i, 1)))).contDiff)

/-- The actual signed Moore determinant as a smooth map of Hölder fields. -/
def mooreDetField (hα : 0 ≤ α) (n : ℕ)
    (A : HolderMap X (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α) : HolderMap X ℝ α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.map Complex.reCLM (pfaffianField hα n A)

@[simp] theorem value_mooreDetField (hα : 0 ≤ α) (n : ℕ)
    (A : HolderMap X (Matrix (Fin n) (Fin n) (Quaternion ℝ)) α) (x : X) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (mooreDetField hα n A) x = OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x) := by
  rw [mooreDetField, OAI.Analysis.Normed.Function.Holder.HolderMap.value_map, value_pfaffianField]
  rfl

theorem contDiff_mooreDetField (hα : 0 ≤ α) (n : ℕ) (k : ℕ∞ω) :
    ContDiff ℝ k (mooreDetField (X := X) hα n) :=
  (OAI.Analysis.Normed.Function.Holder.HolderMap.mapCLM Complex.reCLM).contDiff.comp (contDiff_pfaffianField hα n k)

end OAI.Analysis.Normed.Function.Holder
