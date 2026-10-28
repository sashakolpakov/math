import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Galois Trace Matrix -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.GaloisTraceMatrix

noncomputable section

/-! Entrywise field trace on matrices, and the Galois-sum formula
after evaluation in any commutative algebra over the base field. -/

open scoped Classical

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {n : ℕ}

def fieldTraceMatrix : Matrix (Fin n) (Fin n) E →ₗ[F] Matrix (Fin n) (Fin n) F where
  toFun X := X.map (Algebra.trace F E)
  map_add' X Y := by ext i j; exact map_add (Algebra.trace F E) _ _
  map_smul' c X := by ext i j; exact (Algebra.trace F E).map_smul c _

omit [FiniteDimensional F E] in
theorem fieldTraceMatrix_algebraMap (X : Matrix (Fin n) (Fin n) F) :
    fieldTraceMatrix (X.map (algebraMap F E)) = (Module.finrank F E : F) • X := by
  ext i j
  simpa only [fieldTraceMatrix, LinearMap.coe_mk, AddHom.coe_mk, Matrix.map_apply,
    Matrix.smul_apply, Nat.cast_smul_eq_nsmul] using Algebra.trace_algebraMap (S := E) (X i j)

theorem mapped_fieldTraceMatrix [IsGalois F E]
    {A : Type*} [CommRing A] [Algebra F A] (f : E →ₐ[F] A)
    (X : Matrix (Fin n) (Fin n) E) :
    (fieldTraceMatrix X).map (algebraMap F A) =
      ∑ σ : E ≃ₐ[F] E, X.map (f.comp σ.toAlgHom) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.sum_apply]
  change algebraMap F A (Algebra.trace F E (X i j)) = ∑ σ : E ≃ₐ[F] E, f (σ (X i j))
  rw [← map_sum, ← trace_eq_sum_automorphisms, f.commutes]

theorem fieldTraceMatrix_mem_span_of_mem_span [CharZero F]
    (X : Matrix (Fin n) (Fin n) F) (s : Set (Matrix (Fin n) (Fin n) E))
    (hX : X.map (algebraMap F E) ∈ Submodule.span E s) :
    X ∈ Submodule.span F {Z | ∃ a : E, ∃ Y ∈ s, Z = fieldTraceMatrix (F := F) (a • Y)} := by
  let W := Submodule.span F {Z | ∃ a : E, ∃ Y ∈ s, Z = fieldTraceMatrix (F := F) (a • Y)}
  have htrace : ∀ Y ∈ Submodule.span E s, ∀ a : E, fieldTraceMatrix (F := F) (a • Y) ∈ W := by
    intro Y hY
    induction hY using Submodule.span_induction with
    | mem Y hY => exact fun a => Submodule.subset_span ⟨a, Y, hY, rfl⟩
    | zero => intro a; simpa only [smul_zero, map_zero] using W.zero_mem
    | add Y Z _ _ hY hZ =>
      intro a
      simpa only [smul_add, map_add] using W.add_mem (hY a) (hZ a)
    | smul c Y _ hY =>
      intro a
      simpa only [smul_smul] using hY (a * c)
  have h := htrace _ hX 1
  rw [one_smul, fieldTraceMatrix_algebraMap] at h
  have hd : (Module.finrank F E : F) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos.ne')
  exact (W.smul_mem_iff hd).mp h

end

end OAI.NumberTheory.Quaternion.Arithmetic.GaloisTraceMatrix
