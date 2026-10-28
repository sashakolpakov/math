import OAI.Analysis.HodgeTheory.Decomposition.SchwartzCoordinates

/-! # Rellich Energy -/

namespace OAI.Analysis.HodgeTheory.Decomposition.RellichEnergy.Constructions

noncomputable section

/-! Vector-valued Rellich compactness from the actual L² norms of the
function and its ordinary first derivatives. -/

open _root_.MeasureTheory LineDeriv
open scoped SchwartzMap BigOperators

variable {E F ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι] [Fintype κ]

theorem schwartz_coordinate_sobolev_of_energy
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℂ F) (j : κ)
    (f : 𝓢(E, F)) (C : ℝ) (hC : 0 ≤ C)
    (hf : ‖f.toLp 2 volume‖ ^ 2 + (∑ i, ‖(∂_{b i} f).toLp 2 volume‖ ^ 2) ≤ C ^ 2) :
    AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.schwartzSobolevNorm 1 (SchwartzCoordinates.Constructions.schwartzOrthonormalCoordinate c j f) ≤
      C * (1 + ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * Fintype.card ι) := by
  have hnorm : ‖f.toLp 2 volume‖ ≤ C := by
    apply (sq_le_sq₀ (norm_nonneg _) hC).mp
    exact (le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => sq_nonneg _))).trans hf
  have hd (i : ι) : ‖(∂_{b i} f).toLp 2 volume‖ ≤ C := by
    apply (sq_le_sq₀ (norm_nonneg _) hC).mp
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
      sq_nonneg ‖(∂_{b j} f).toLp 2 volume‖) (Finset.mem_univ i)
    exact hi.trans ((le_add_of_nonneg_left (sq_nonneg ‖f.toLp 2 volume‖)).trans hf)
  have hsum : (∑ i, ‖(∂_{b i} f).toLp 2 volume‖) ≤ Fintype.card ι * C := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      (Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hd i))
  calc
    _ ≤ ‖f.toLp 2 volume‖ + ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ *
        ∑ i, ‖(∂_{b i} f).toLp 2 volume‖ := SchwartzCoordinates.Constructions.schwartzOrthonormalCoordinate_sobolev_bound b c j f
    _ ≤ C + ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * (Fintype.card ι * C) :=
      add_le_add hnorm (mul_le_mul_of_nonneg_left hsum (norm_nonneg _))
    _ = _ := by ring

theorem schwartz_vector_rellich_energy
    (b : OrthonormalBasis ι ℝ E) (c : OrthonormalBasis κ ℂ F)
    {K : Set E} (hK : IsCompact K) (C : ℝ) (hC : 0 ≤ C) :
    IsCompact (closure ((fun f : 𝓢(E, F) => f.toLp 2 volume) ''
      {f | Function.support f ⊆ K ∧
        ‖f.toLp 2 volume‖ ^ 2 + (∑ i, ‖(∂_{b i} f).toLp 2 volume‖ ^ 2) ≤ C ^ 2})) := by
  have h := SchwartzCoordinates.Constructions.schwartz_vector_rellich_compact c hK
    (C * (1 + ‖(2 * Real.pi * Complex.I : ℂ)⁻¹‖ * Fintype.card ι))
  apply h.of_isClosed_subset isClosed_closure
  apply closure_mono
  rintro _ ⟨f, ⟨hf, henergy⟩, rfl⟩
  exact ⟨f, ⟨hf, fun j => schwartz_coordinate_sobolev_of_energy b c j f C hC henergy⟩, rfl⟩

end

end OAI.Analysis.HodgeTheory.Decomposition.RellichEnergy.Constructions
