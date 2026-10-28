import Mathlib.FieldTheory.NormalizedTrace
import Mathlib.NumberTheory.NumberField.Basic

/-! # Normalized Trace Spectrum -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.NormalizedTraceSpectrum.Construction

noncomputable section

/-! Normalized trace supplies rational eigenvalue weights and commutes
with automorphisms of every algebraic characteristic-zero field. -/

def normalizedTraceSpectralMap
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] [Algebra.IsIntegral k K] :
    K →+ K :=
  (algebraMap k K).toAddMonoidHom.comp (Algebra.normalizedTrace k K).toAddMonoidHom

theorem normalizedTraceSpectralMap_apply
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] [Algebra.IsIntegral k K]
    (x : K) : normalizedTraceSpectralMap (k := k) x =
      algebraMap k K (Algebra.normalizedTrace k K x) := rfl

theorem normalizedTraceSpectralMap_one
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] [Algebra.IsIntegral k K] :
    normalizedTraceSpectralMap (k := k) (1 : K) = 1 := by
  rw [normalizedTraceSpectralMap_apply, ← map_one (algebraMap k K),
    Algebra.normalizedTrace_algebraMap_apply_eq_self]

theorem normalizedTraceSpectralMap_equivariant
    {k K : Type} [Field k] [CharZero k] [Field K] [Algebra k K] [Algebra.IsIntegral k K]
    (σ : K ≃ₐ[k] K) (x : K) :
    σ (normalizedTraceSpectralMap (k := k) x) = normalizedTraceSpectralMap (k := k) (σ x) := by
  have h : Algebra.normalizedTrace k K (σ x) = Algebra.normalizedTrace k K x :=
    Algebra.normalizedTrace_map k K σ.toAlgHom x
  simp only [normalizedTraceSpectralMap_apply, σ.commutes, h]

theorem rational_normalizedTraceSpectralMap_equivariant
    {k K : Type} [Field k] [CharZero k] [Field K] [CharZero K]
    [Algebra k K] [Algebra.IsIntegral ℚ K] (σ : K ≃ₐ[k] K) (x : K) :
    σ (normalizedTraceSpectralMap (k := ℚ) x) = normalizedTraceSpectralMap (k := ℚ) (σ x) := by
  exact normalizedTraceSpectralMap_equivariant (σ.restrictScalars ℚ) x

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.NormalizedTraceSpectrum.Construction
