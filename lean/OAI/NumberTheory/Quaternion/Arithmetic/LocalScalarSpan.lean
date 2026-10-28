import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Local Scalar Span -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LocalScalarSpan

noncomputable section

/-! Membership for every independent local scalar multiple is
preserved under linear span over the global base field. -/

open scoped Classical

variable {F κ ι : Type*} [Field F] [Field κ] {K A : ι → Type*}
  [∀ i, Field (K i)] [∀ i, CommRing (A i)] [∀ i, Algebra F (K i)]
  [∀ i, Algebra F (A i)] [∀ i, Algebra (K i) (A i)] [∀ i, Algebra κ (A i)]
  [∀ i, IsScalarTower F (K i) (A i)] {n : ℕ}

def locallyScaledMatrix (X : Matrix (Fin n) (Fin n) F) (b : ∀ i, K i) :
    ∀ i, Matrix (Fin n) (Fin n) (A i) :=
  fun i => b i • X.map (algebraMap F (A i))

omit [Field κ] [∀ i, Algebra κ (A i)] in
theorem locallyScaledMatrix_smul (c : F) (X : Matrix (Fin n) (Fin n) F) (b : ∀ i, K i) :
    locallyScaledMatrix (A := A) (c • X) b =
      locallyScaledMatrix (A := A) X (fun i => b i * algebraMap F (K i) c) := by
  funext i
  ext j k
  simp only [locallyScaledMatrix, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  simp only [Algebra.smul_def]
  rw [map_mul, map_mul, ← IsScalarTower.algebraMap_apply F (K i) (A i), mul_assoc]

theorem locallyScaledMatrix_mem_of_span
    (W : Submodule κ (∀ i, Matrix (Fin n) (Fin n) (A i)))
    (s : Set (Matrix (Fin n) (Fin n) F))
    (hs : ∀ X ∈ s, ∀ b : ∀ i, K i, locallyScaledMatrix (A := A) X b ∈ W)
    {X : Matrix (Fin n) (Fin n) F} (hX : X ∈ Submodule.span F s) :
    ∀ b : ∀ i, K i, locallyScaledMatrix (A := A) X b ∈ W := by
  induction hX using Submodule.span_induction with
  | mem X hX => exact hs X hX
  | zero =>
    intro b
    have he : locallyScaledMatrix (A := A) (0 : Matrix (Fin n) (Fin n) F) b = 0 := by
      funext i
      ext j k
      simp [locallyScaledMatrix]
    rw [he]
    exact W.zero_mem
  | add X Y _ _ hX hY =>
    intro b
    have he : locallyScaledMatrix (A := A) (X + Y) b =
        locallyScaledMatrix (A := A) X b + locallyScaledMatrix (A := A) Y b := by
      funext i
      ext j k
      simp [locallyScaledMatrix, smul_add]
    rw [he]
    exact W.add_mem (hX b) (hY b)
  | smul c X _ hX =>
    intro b
    rw [locallyScaledMatrix_smul]
    exact hX _

end

end OAI.NumberTheory.Quaternion.Arithmetic.LocalScalarSpan
