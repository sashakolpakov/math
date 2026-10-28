import OAI.RepresentationTheory.Weil.Local.FunctionsMetaplectic

/-! # Coordinates -/

namespace OAI.RepresentationTheory.Weil.Local.Coordinates.Construction

noncomputable section

/-! A complete locally compact characteristic-zero normed field is either
ultrametric or admits finite-dimensional real additive coordinates. This is
the part of the local-field dichotomy needed for nonzero Bruhat vectors. -/

open Filter
open scoped _root_.Topology

variable (F : Type) [NormedField F] [CharZero F]

def rationalNorm : AbsoluteValue ℚ ℝ where
  toFun q := ‖(q : F)‖
  map_mul' q r := by simp [norm_mul]
  nonneg' q := norm_nonneg _
  eq_zero' q := by simp
  add_le' q r := by simpa using norm_add_le (q : F) (r : F)

theorem rationalCast_uniformContinuous_of_unbounded
    (h : ¬ ∀ n : ℕ, ‖(n : F)‖ ≤ 1) :
    UniformContinuous (Rat.castHom F : ℚ → F) := by
  have hh : ¬ ∀ n : ℕ, rationalNorm F n ≤ 1 := by
    simpa [rationalNorm] using h
  have he := Rat.AbsoluteValue.equiv_real_of_unbounded hh
  obtain ⟨s, hs, heq⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp he.symm
  have hp (q : ℚ) : ‖(q : F)‖ = ‖q‖ ^ s := by
    have hq := congrFun heq q
    simpa [rationalNorm, Rat.AbsoluteValue.real_eq_abs, ← Real.norm_eq_abs,
      Rat.norm_cast_real] using hq.symm
  apply uniformContinuous_of_continuousAt_zero (Rat.castHom F).toAddMonoidHom
  rw [ContinuousAt, map_zero]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  change Tendsto (fun q : ℚ => ‖(q : F)‖) (𝓝 0) (𝓝 0)
  simp_rw [hp]
  have hc : ContinuousAt (fun q : ℚ => ‖q‖ ^ s) 0 :=
    continuous_norm.continuousAt.rpow_const (Or.inr hs.le)
  simpa [Real.zero_rpow hs.ne'] using hc.tendsto

variable [CompleteSpace F]

def realEmbeddingOfUnbounded (h : ¬ ∀ n : ℕ, ‖(n : F)‖ ≤ 1) : ℝ →+* F :=
  IsDenseInducing.extendRingHom
    (i := Rat.castHom ℝ) (f := Rat.castHom F)
    Rat.isUniformEmbedding_coe_real.isUniformInducing Rat.denseRange_cast
    (rationalCast_uniformContinuous_of_unbounded F h)

theorem realEmbeddingOfUnbounded_continuous
    (h : ¬ ∀ n : ℕ, ‖(n : F)‖ ≤ 1) :
    Continuous (realEmbeddingOfUnbounded F h) :=
  (uniformContinuous_uniformly_extend
    Rat.isUniformEmbedding_coe_real.isUniformInducing Rat.denseRange_cast
    (rationalCast_uniformContinuous_of_unbounded F h)).continuous

theorem exists_real_coordinates_of_unbounded [LocallyCompactSpace F]
    (h : ¬ ∀ n : ℕ, ‖(n : F)‖ ≤ 1) (d : ℕ) :
    ∃ r : ℕ, Nonempty ((Fin r → ℝ) ≃ₜ+ FunctionsMetaplectic.Construction.Position F d) := by
  let : Algebra ℝ F := (realEmbeddingOfUnbounded F h).toAlgebra
  let : ContinuousSMul ℝ F := continuousSMul_of_algebraMap ℝ F
    (realEmbeddingOfUnbounded_continuous F h)
  let : FiniteDimensional ℝ F := FiniteDimensional.of_locallyCompactSpace ℝ
  let b := Module.finBasis ℝ (FunctionsMetaplectic.Construction.Position F d)
  exact ⟨Module.finrank ℝ (FunctionsMetaplectic.Construction.Position F d), ⟨b.equivFunL.symm.toContinuousAddEquiv⟩⟩

end

end OAI.RepresentationTheory.Weil.Local.Coordinates.Construction
