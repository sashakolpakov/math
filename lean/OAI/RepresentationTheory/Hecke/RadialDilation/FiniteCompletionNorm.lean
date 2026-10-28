import OAI.RepresentationTheory.Hecke.RadialDilation.SplitScalarPowerBounds
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Finite Completion Norm -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.FiniteCompletionNorm.Realization

noncomputable section

section

/-! Norms in finite completions read the original number-field valuations. -/

open scoped Classical
open IsDedekindDomain _root_.NumberField WithZeroMulInt

variable (E : Type*) [Field E] [NumberField E]
  (w : HeightOneSpectrum (𝓞 E))

theorem finiteCompletion_algebraMap (x : E) :
    algebraMap E (w.adicCompletion E) x = FinitePlace.embedding w x := rfl

theorem finiteCompletion_norm_le_one (x : E) (hx : w.valuation E x ≤ 1) :
    ‖algebraMap E (w.adicCompletion E) x‖ ≤ 1 := by
  rw [finiteCompletion_algebraMap, FinitePlace.norm_embedding']
  exact_mod_cast (toNNReal_le_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal w)).mpr hx

theorem finiteCompletion_norm_eq_one (x : E) (hx : w.valuation E x = 1) :
    ‖algebraMap E (w.adicCompletion E) x‖ = 1 := by
  rw [finiteCompletion_algebraMap, FinitePlace.norm_embedding', hx, map_one, NNReal.coe_one]

@[instance_reducible]
def finiteCompletionNontriviallyNormedField : NontriviallyNormedField (w.adicCompletion E) := by
  apply NontriviallyNormedField.ofNormNeOne
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.coe_ne_zero hπ.symm
  have hn : ‖FinitePlace.embedding w π‖ < 1 := by
    rw [FinitePlace.norm_embedding']
    have hv : w.valuation E π < 1 := by
      rw [hπ, ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by norm_num)
    exact_mod_cast (toNNReal_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal w)).mpr hv
  exact ⟨FinitePlace.embedding w π,
    (map_ne_zero (FinitePlace.embedding w)).mpr hπ0, hn.ne⟩

end

/-! Valuation bounds on the Galois conjugates bound the rational scalar matrix in a finite completion. -/

open scoped Classical _root_.Matrix
open IsDedekindDomain _root_.NumberField

theorem rational_scalar_finite_completion_bounds
    (E : Type*) [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    (w : HeightOneSpectrum (𝓞 E)) {I : Type*} [Fintype I] [DecidableEq I]
    (e : (Fin 3 → E) ≃ₗ[ℚ] (I → ℚ)) (r : E)
    (hr : ∀ σ : E ≃ₐ[ℚ] E, w.valuation E (σ r) ≤ 1) :
    ∃ R : ℝ, ∀ (N : ℕ) i j,
      ‖((RationalCoordinates.Realization.rationalScalarMatrix E e r).map (algebraMap ℚ (w.adicCompletion E)) ^ N) i j‖ ≤ R := by
  let : NontriviallyNormedField (w.adicCompletion E) := finiteCompletionNontriviallyNormedField E w
  apply SplitScalarPowerBounds.Realization.rational_scalar_split_power_bounds E (w.adicCompletion E) e r
  intro σ
  obtain ⟨τ, rfl⟩ := (Normal.algHomEquivAut ℚ (w.adicCompletion E) E).symm.surjective σ
  change ‖algebraMap E (w.adicCompletion E) (τ r)‖ ≤ 1
  exact finiteCompletion_norm_le_one E w (τ r) (hr τ)

end

end OAI.RepresentationTheory.Hecke.RadialDilation.FiniteCompletionNorm.Realization
