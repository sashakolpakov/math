import OAI.Analysis.HodgeTheory.Decomposition.SymbolDifferential
import OAI.Analysis.HodgeTheory.Decomposition.AdjointCoefficients

/-! # Symbol Ellipticity -/

namespace OAI.Analysis.HodgeTheory.Decomposition.SymbolEllipticity.Constructions

noncomputable section

section

/-! Positive principal-symbol energy of the actual metric Hodge operator.
Exactness of the exterior symbol excludes simultaneous vanishing of its
forward and metric-adjoint symbols. -/

open scoped BigOperators

section Energy

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

omit [CompleteSpace E] in
theorem positiveOperator_nonneg (A : E →L[ℝ] E)
    (hA : ∀ u : E, u ≠ 0 → 0 < inner ℝ (A u) u) (u : E) : 0 ≤ inner ℝ (A u) u := by
  by_cases hu : u = 0
  · rw [hu, inner_zero_right]
  · exact (hA u hu).le

theorem exact_symbol_energy_positive
    (P : E →L[ℝ] F) (Q : F →L[ℝ] G)
    (A : E →L[ℝ] E) (B : F →L[ℝ] F) (C : G →L[ℝ] G)
    (hA : ∀ u : E, u ≠ 0 → 0 < inner ℝ (A u) u)
    (hB : ∀ u : F, u ≠ 0 → 0 < inner ℝ (B u) u)
    (hC : ∀ u : G, u ≠ 0 → 0 < inner ℝ (C u) u)
    (hAi : A.IsInvertible) (hex : ∀ u : F, Q u = 0 → ∃ v : E, P v = u)
    (u : F) (hu : u ≠ 0) :
    0 < inner ℝ (C (Q u)) (Q u) +
      inner ℝ (A (A.inverse (P.adjoint (B u)))) (A.inverse (P.adjoint (B u))) := by
  have hnon : 0 ≤ inner ℝ (A (A.inverse (P.adjoint (B u)))) (A.inverse (P.adjoint (B u))) :=
    positiveOperator_nonneg A hA _
  by_cases hQ : Q u = 0
  · obtain ⟨v, hv⟩ := hex u hQ
    have hL : A.inverse (P.adjoint (B u)) ≠ 0 := by
      intro hz
      have hPA : P.adjoint (B u) = 0 := by
        have h := hAi.self_apply_inverse (P.adjoint (B u))
        rw [hz, map_zero] at h
        exact h.symm
      have hpair : inner ℝ (B u) u = 0 := by
        calc
          _ = inner ℝ (B u) (P v) := congrArg (fun w => inner ℝ (B u) w) hv.symm
          _ = inner ℝ (P.adjoint (B u)) v := (P.adjoint_inner_left _ _).symm
          _ = 0 := by rw [hPA, inner_zero_left]
      exact (ne_of_gt (hB u hu)) hpair
    rw [hQ, map_zero, inner_zero_left, zero_add]
    exact hA _ hL
  · exact add_pos_of_pos_of_nonneg (hC _ hQ) hnon

end Energy

section Coordinates

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

def coordinateCovectorSymbol (b : Module.Basis ι ℝ E) (n : ℕ) (ξ : E →L[ℝ] ℝ) :
    SymbolDifferential.Constructions.ExteriorCoordinates ι n →L[ℝ] SymbolDifferential.Constructions.ExteriorCoordinates ι (n + 1) :=
  ((SymbolDifferential.Constructions.exteriorCoordinateEquiv b (n + 1)).toContinuousLinearMap.restrictScalars ℝ).comp
    ((SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ).comp
      ((SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm.toContinuousLinearMap.restrictScalars ℝ))

theorem coordinateCovectorSymbol_exact (b : Module.Basis ι ℝ E) (n : ℕ)
    (ξ : E →L[ℝ] ℝ) (hξ : ξ ≠ 0) (a : SymbolDifferential.Constructions.ExteriorCoordinates ι (n + 1))
    (ha : coordinateCovectorSymbol b (n + 1) ξ a = 0) :
    ∃ c : SymbolDifferential.Constructions.ExteriorCoordinates ι n, coordinateCovectorSymbol b n ξ c = a := by
  have hraw : SymbolDifferential.Constructions.exteriorDifferentialSymbol (n + 1) ξ ((SymbolDifferential.Constructions.exteriorCoordinateEquiv b (n + 1)).symm a) = 0 := by
    apply (SymbolDifferential.Constructions.exteriorCoordinateEquiv b (n + 1 + 1)).injective
    rw [map_zero]
    exact ha
  obtain ⟨c, hc⟩ := SymbolDifferential.Constructions.exteriorSymbol_exact n ξ hξ _ hraw
  refine ⟨SymbolDifferential.Constructions.exteriorCoordinateEquiv b n c, ?_⟩
  change SymbolDifferential.Constructions.exteriorCoordinateEquiv b (n + 1)
    (SymbolDifferential.Constructions.exteriorDifferentialSymbol n ξ ((SymbolDifferential.Constructions.exteriorCoordinateEquiv b n).symm (SymbolDifferential.Constructions.exteriorCoordinateEquiv b n c))) = a
  rw [ContinuousLinearEquiv.symm_apply_apply, hc, ContinuousLinearEquiv.apply_symm_apply]

end Coordinates

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

include he

/-- Positive symbol energy for the actual projective metric, at every nonzero real covector. -/
theorem projective_hodge_symbol_positive (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (hz : z ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e)
    (ξ : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ) (hξ : ξ ≠ 0)
    (u : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (hu : u ≠ 0) :
    let basis := (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let P := coordinateCovectorSymbol basis n ξ
    let Q := coordinateCovectorSymbol basis (n + 1) ξ
    let A := AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n z
    let B := AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1) z
    let C := AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1 + 1) z
    0 < inner ℝ (C (Q u)) (Q u) +
      inner ℝ (A (A.inverse (P.adjoint (B u)))) (A.inverse (P.adjoint (B u))) := by
  dsimp only
  apply exact_symbol_energy_positive
  · exact AdjointCoefficients.Constructions.projectiveWeightedFormOperator_positive V e he n z hz
  · exact AdjointCoefficients.Constructions.projectiveWeightedFormOperator_positive V e he (n + 1) z hz
  · exact AdjointCoefficients.Constructions.projectiveWeightedFormOperator_positive V e he (n + 1 + 1) z hz
  · exact AdjointCoefficients.Constructions.projectiveWeightedFormOperator_isInvertible V e he n z hz
  · exact fun a ha => coordinateCovectorSymbol_exact _ n ξ hξ a ha
  · exact hu

end

/-! Uniform positive Hodge-symbol energy on compact coordinate sets and
unit covectors and unit form coefficients. -/

open scoped ContDiff

section SymbolContinuity

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [LinearOrder ι]

theorem coordinateCovectorSymbol_continuous (b : Module.Basis ι ℝ E) (n : ℕ) :
    Continuous (coordinateCovectorSymbol b n) := by
  have h : Continuous (SymbolDifferential.Constructions.exteriorDifferentialSymbol (E := E) n) := by
    unfold SymbolDifferential.Constructions.exteriorDifferentialSymbol
    exact continuous_const.clm_comp (ContinuousLinearMap.smulRightL ℝ E (DifferentialForms.Manifold.Basic.FormValue E n)).continuous
  unfold coordinateCovectorSymbol
  exact continuous_const.clm_comp (h.clm_comp continuous_const)

theorem coordinateCovectorSymbol_smul (b : Module.Basis ι ℝ E) (n : ℕ)
    (ξ : E →L[ℝ] ℝ) (r : ℝ) :
    coordinateCovectorSymbol b n (r • ξ) = r • coordinateCovectorSymbol b n ξ := by
  unfold coordinateCovectorSymbol SymbolDifferential.Constructions.exteriorDifferentialSymbol
  rw [map_smul]
  apply ContinuousLinearMap.ext
  intro a
  simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul]

end SymbolContinuity

variable (V : AlgebraicGeometry.Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace) (n : ℕ)

abbrev ProjectiveSymbolParameters := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V ×
  ((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ) × SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1))

def projectiveHodgeSymbolEnergy (p : ProjectiveSymbolParameters V n) : ℝ :=
  let basis := (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  let P := coordinateCovectorSymbol basis n p.2.1
  let Q := coordinateCovectorSymbol basis (n + 1) p.2.1
  let A := AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n p.1
  let B := AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1) p.1
  let C := AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e (n + 1 + 1) p.1
  let w := A.inverse (P.adjoint (B p.2.2))
  inner ℝ (C (Q p.2.2)) (Q p.2.2) + inner ℝ (A w) w

theorem projectiveHodgeSymbolEnergy_smul (z : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
    (ξ : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ)
    (u : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) (r s : ℝ) :
    projectiveHodgeSymbolEnergy V e n (z, r • ξ, s • u) =
      r ^ 2 * s ^ 2 * projectiveHodgeSymbolEnergy V e n (z, ξ, u) := by
  unfold projectiveHodgeSymbolEnergy
  dsimp only
  simp only [coordinateCovectorSymbol_smul, map_smul, smul_apply,
    real_inner_smul_left, real_inner_smul_right]
  ring

include he

theorem projectiveHodgeSymbolEnergy_continuousOn :
    ContinuousOn (projectiveHodgeSymbolEnergy V e n)
      {p : ProjectiveSymbolParameters V n | p.1 ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e} := by
  let U : Set (ProjectiveSymbolParameters V n) := {p | p.1 ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e}
  let basis := (stdOrthonormalBasis ℝ (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
  have hW (k : ℕ) : ContinuousOn (fun p : ProjectiveSymbolParameters V n =>
      AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e k p.1) U :=
    (AdjointCoefficients.Constructions.projectiveWeightedFormOperator_smooth V e he k).continuousOn.comp continuous_fst.continuousOn
      (fun _ hp => hp)
  have hI : ContinuousOn (fun p : ProjectiveSymbolParameters V n =>
      (AdjointCoefficients.Constructions.projectiveWeightedFormOperator V e n p.1).inverse) U :=
    (AdjointCoefficients.Constructions.projectiveWeightedFormOperator_inverse_smooth V e he n).continuousOn.comp continuous_fst.continuousOn
      (fun _ hp => hp)
  have hS (k : ℕ) : ContinuousOn (fun p : ProjectiveSymbolParameters V n =>
      coordinateCovectorSymbol basis k p.2.1) U :=
    (coordinateCovectorSymbol_continuous basis k).comp_continuousOn
      (continuous_fst.comp continuous_snd).continuousOn
  have hu : ContinuousOn (fun p : ProjectiveSymbolParameters V n => p.2.2) U :=
    (continuous_snd.comp continuous_snd).continuousOn
  have hP : ContinuousOn (fun p : ProjectiveSymbolParameters V n =>
      (coordinateCovectorSymbol basis n p.2.1).adjoint) U :=
    ContinuousLinearMap.adjoint.continuous.comp_continuousOn (hS n)
  have hw := hI.clm_apply (hP.clm_apply ((hW (n + 1)).clm_apply hu))
  exact ((hW (n + 1 + 1)).clm_apply ((hS (n + 1)).clm_apply hu)).inner
    ((hS (n + 1)).clm_apply hu) |>.add (((hW n).clm_apply hw).inner hw)

/-- The positive symbol has a uniform lower bound on each compact chart set, without dimension exclusions. -/
theorem projectiveHodgeSymbolEnergy_uniform {K : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)}
    (hK : IsCompact K) (hKU : K ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, ∀ ξ : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ, ‖ξ‖ = 1 →
      ∀ u : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1), ‖u‖ = 1 →
        c ≤ projectiveHodgeSymbolEnergy V e n (z, ξ, u) := by
  let S := K ×ˢ (Metric.sphere (0 : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ) 1 ×ˢ
    Metric.sphere (0 : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1)) 1)
  have hS : IsCompact S := hK.prod ((isCompact_sphere _ _).prod (isCompact_sphere _ _))
  have hc := (projectiveHodgeSymbolEnergy_continuousOn V e he n).mono
    (show S ⊆ {p : ProjectiveSymbolParameters V n | p.1 ∈ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e} from
      fun _ hp => hKU hp.1)
  obtain ⟨c, hcp, hcl⟩ := hS.exists_forall_le' hc (a := (0 : ℝ)) (by
    intro p hp
    have hξ : p.2.1 ≠ 0 := by
      intro hz
      have hn : ‖p.2.1‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hp.2.1
      rw [hz, norm_zero] at hn
      exact zero_ne_one hn
    have hu : p.2.2 ≠ 0 := by
      intro hz
      have hn : ‖p.2.2‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using hp.2.2
      rw [hz, norm_zero] at hn
      exact zero_ne_one hn
    exact projective_hodge_symbol_positive V e he n p.1 (hKU hp.1) p.2.1 hξ p.2.2 hu)
  refine ⟨c, hcp, fun z hz ξ hξ u hu => hcl (z, ξ, u) ?_⟩
  exact ⟨hz, by simpa only [Metric.mem_sphere, dist_zero_right] using hξ,
    by simpa only [Metric.mem_sphere, dist_zero_right] using hu⟩

/-- The actual Hodge-symbol energy controls the squared covector and form norms uniformly. -/
theorem projectiveHodgeSymbolEnergy_coercive {K : Set (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)}
    (hK : IsCompact K) (hKU : K ⊆ AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanDomain V e) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, ∀ ξ : AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V →L[ℝ] ℝ,
      ∀ u : SymbolDifferential.Constructions.ExteriorCoordinates (AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) (n + 1),
        c * ‖ξ‖ ^ 2 * ‖u‖ ^ 2 ≤ projectiveHodgeSymbolEnergy V e n (z, ξ, u) := by
  obtain ⟨c, hc, hbound⟩ := projectiveHodgeSymbolEnergy_uniform V e he n hK hKU
  refine ⟨c, hc, fun z hz ξ u => ?_⟩
  by_cases hξ : ξ = 0
  · subst ξ
    have h := projectiveHodgeSymbolEnergy_smul V e n z 0 u 0 1
    simp only [zero_smul, one_smul, zero_pow (by decide : 2 ≠ 0), one_pow, zero_mul] at h
    rw [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, h]
  · by_cases hu : u = 0
    · subst u
      have h := projectiveHodgeSymbolEnergy_smul V e n z ξ 0 1 0
      simp only [zero_smul, one_smul, zero_pow (by decide : 2 ≠ 0), one_pow, mul_zero, zero_mul] at h
      rw [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, h]
    · let η := (‖ξ‖⁻¹ : ℝ) • ξ
      let v := (‖u‖⁻¹ : ℝ) • u
      have hη : ‖η‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hξ
      have hv : ‖v‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hu
      have hξη : ‖ξ‖ • η = ξ := by
        dsimp only [η]
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hξ), one_smul]
      have huv : ‖u‖ • v = u := by
        dsimp only [v]
        rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu), one_smul]
      have hscale := projectiveHodgeSymbolEnergy_smul V e n z η v ‖ξ‖ ‖u‖
      rw [hξη, huv] at hscale
      rw [hscale]
      nlinarith [mul_le_mul_of_nonneg_left (hbound z hz η hη v hv)
        (mul_nonneg (sq_nonneg ‖ξ‖) (sq_nonneg ‖u‖))]

end

end OAI.Analysis.HodgeTheory.Decomposition.SymbolEllipticity.Constructions
