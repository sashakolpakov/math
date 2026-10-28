import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevInv
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpComponents
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoerciveKernelSolver

/-! # Gradient Support -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GradientSupport.CM.Construction

noncomputable section

section

/-! Weak variable-coefficient equations on the genuine supported Sobolev space. -/

open _root_.MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι]

/-- Assemble the actual normalized weak derivatives into an L2 vector field. -/
def supportedH1VectorGradient (b : OrthonormalBasis ι ℝ E) (K : Set E) :
    SobolevIs.CM.Construction.supportedH1Coordinates K →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E) :=
  (LpComponents.CM.Construction.lpOrthonormalSynthesis (EuclideanSpace.basisFun ι ℂ)).comp (SobolevInv.CM.Construction.supportedH1Gradient b K)

theorem supportedH1VectorGradient_norm (b : OrthonormalBasis ι ℝ E) (K : Set E)
    (u : SobolevIs.CM.Construction.supportedH1Coordinates K) :
    ‖supportedH1VectorGradient b K u‖ = ‖SobolevInv.CM.Construction.supportedH1Gradient b K u‖ :=
  (LpComponents.CM.Construction.lpOrthonormalSynthesisIsometry (EuclideanSpace.basisFun ι ℂ)).norm_map _

theorem supportedH1VectorGradient_poincare [Nontrivial E] (b : OrthonormalBasis ι ℝ E)
    {K : Set E} (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : SobolevIs.CM.Construction.supportedH1Coordinates K, c * ‖u‖ ≤ ‖supportedH1VectorGradient b K u‖ := by
  obtain ⟨c, hc, hbound⟩ := CoerciveEnergy.CM.Construction.graphEnergy_poincare_bound (SobolevIs.CM.Construction.supportedH1Embedding K) (SobolevInv.CM.Construction.supportedH1Gradient b K)
    (SobolevIs.CM.Construction.supportedH1Embedding_isCompact hK)
    ((FourierEnergy.CM.Construction.sobolevNormalizedGradient_injective b).comp Subtype.val_injective)
    (fun u v => FourierEnergy.CM.Construction.sobolev_graph_inner b u.val v.val)
  exact ⟨c, hc, fun u => (hbound u).trans_eq (supportedH1VectorGradient_norm b K u).symm⟩

/-- Every bounded real forcing functional has a unique weak solution for a
bounded measurable uniformly positive coefficient acting on the actual
normalized Sobolev gradient. -/
theorem variable_dirichlet_weak_existsUnique [Nontrivial E] (b : OrthonormalBasis ι ℝ E)
    {K : Set E} (hK : IsCompact K)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι)
    (hA : AEStronglyMeasurable A (volume : Measure E))
    {C a : ℝ} (hC : ∀ᵐ x ∂(volume : Measure E), ‖A x‖ ≤ C) (ha : 0 < a)
    (hpos : ∀ᵐ x ∂(volume : Measure E), ∀ w : EuclideanSpace ℂ ι,
      a * ‖w‖ * ‖w‖ ≤ inner ℝ (A x w) w)
    (ℓ : SobolevIs.CM.Construction.supportedH1Coordinates K →L[ℝ] ℝ) :
    ∃! u : SobolevIs.CM.Construction.supportedH1Coordinates K, ∀ v : SobolevIs.CM.Construction.supportedH1Coordinates K,
      (∫ x, inner ℝ (A x (supportedH1VectorGradient b K u x))
        (supportedH1VectorGradient b K v x)) = ℓ v := by
  let : InnerProductSpace ℝ (SobolevIs.CM.Construction.supportedH1Coordinates K) := InnerProductSpace.complexToReal
  obtain ⟨c, hc, hD⟩ := supportedH1VectorGradient_poincare b hK
  exact CoerciveKernelSolver.CM.Construction.coefficientDerivative_weak_existsUnique A hA hC hc ha hpos
    ((supportedH1VectorGradient b K).restrictScalars ℝ) hD ℓ

end

/-! The actual weak derivatives of completed supported functions retain support. -/

open _root_.MeasureTheory TemperedDistribution Set
open scoped SchwartzMap LineDeriv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem sobolevL2Derivative_support {K : Set E} (hK : IsClosed K)
    (m : E) (u : SobolevIs.CM.Construction.supportedH1Coordinates K) :
    ∀ᵐ x ∂(volume : Measure E).restrict Kᶜ, SobolevDifferential.CM.Construction.sobolevL2Derivative m u.val x = 0 := by
  let D := SobolevDifferential.CM.Construction.sobolevL2Derivative (F := ℂ) m
  let P : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
    (LpLocalization.CM.Construction.lpSubtypeZeroExtension volume hK.measurableSet).toContinuousLinearMap.comp
      (LpLocalization.CM.Construction.lpSubtypeRestriction volume hK.measurableSet)
  have hclosed : IsClosed {v : Lp ℂ 2 (volume : Measure E) | P (D v) = D v} :=
    isClosed_eq (P.continuous.comp D.continuous) D.continuous
  have hdense : (((SobolevIs.CM.Construction.supportedSchwartzSubmodule K).map (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1)) :
      Set (Lp ℂ 2 (volume : Measure E))) ⊆ {v | P (D v) = D v} := by
    rintro _ ⟨f, hf, rfl⟩
    let g : 𝓢(E, ℂ) := ∂_{m} f
    have hfK : tsupport f ⊆ K :=
      closure_minimal ((SobolevIs.CM.Construction.supportedSchwartzSubmodule_mem_iff K f).mp hf) hK
    have hdf (x : E) (hx : x ∉ K) : g x = 0 := by
      by_contra hn
      exact hx (hfK ((SchwartzMap.tsupport_lineDerivOp_subset m f)
        (subset_closure (show x ∈ Function.support (g : E → ℂ) from hn))))
    change P (SobolevDifferential.CM.Construction.sobolevL2Derivative m (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 f)) =
      SobolevDifferential.CM.Construction.sobolevL2Derivative m (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1 f)
    rw [SobolevDifferential.CM.Construction.sobolevL2Derivative_schwartz]
    change P (g.toLp 2 (volume : Measure E)) = g.toLp 2 (volume : Measure E)
    apply Lp.ext
    filter_upwards [LpLocalization.CM.Construction.lpSubtype_localization_coeFn volume hK.measurableSet
      (g.toLp 2 (volume : Measure E)), g.coeFn_toLp 2 (volume : Measure E)] with x hx hfx
    change P (g.toLp 2 (volume : Measure E)) x = (g.toLp 2 (volume : Measure E)) x
    rw [show P (g.toLp 2 (volume : Measure E)) x = K.indicator
      (fun y => (g.toLp 2 (volume : Measure E)) y) x from hx]
    by_cases hxK : x ∈ K
    · exact Set.indicator_of_mem hxK _
    · rw [Set.indicator_of_notMem hxK, hfx, hdf x hxK]
  have hfixed : P (D u.val) = D u.val := (closure_minimal hdense hclosed) u.property
  have hae := LpLocalization.CM.Construction.lpSubtype_localization_coeFn volume hK.measurableSet (D u.val)
  change P (D u.val) =ᵐ[volume] K.indicator (fun x => D u.val x) at hae
  rw [hfixed] at hae
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem hK.measurableSet.compl] with x hx hk
  exact hx.trans (Set.indicator_of_notMem hk _)

variable {ι : Type*} [Fintype ι]

theorem supportedH1Gradient_support (b : OrthonormalBasis ι ℝ E) {K : Set E} (hK : IsClosed K)
    (u : SobolevIs.CM.Construction.supportedH1Coordinates K) (i : ι) :
    ∀ᵐ x ∂(volume : Measure E).restrict Kᶜ, (SobolevInv.CM.Construction.supportedH1Gradient b K u i) x = 0 := by
  let κ : ℂ := 2 * Real.pi * Complex.I
  have hκ : κ ≠ 0 := by dsimp [κ]; simp [Real.pi_ne_zero]
  have hcoe : ∀ᵐ x ∂(volume : Measure E),
      SobolevDifferential.CM.Construction.sobolevL2Derivative (b i) u.val x = κ * (SobolevInv.CM.Construction.supportedH1Gradient b K u i) x := by
    have h := Lp.coeFn_smul κ (FourierEnergy.CM.Construction.sobolevNormalizedGradient b u.val i)
    rw [← FourierEnergy.CM.Construction.sobolevNormalizedGradient_derivative b u.val i] at h
    exact h
  filter_upwards [sobolevL2Derivative_support hK (b i) u, ae_restrict_of_ae hcoe] with x hx hy
  exact (mul_eq_zero.mp (hy.symm.trans hx)).resolve_left hκ

theorem supportedH1VectorGradient_support (b : OrthonormalBasis ι ℝ E) {K : Set E} (hK : IsClosed K)
    (u : SobolevIs.CM.Construction.supportedH1Coordinates K) :
    ∀ᵐ x ∂(volume : Measure E), x ∉ K → supportedH1VectorGradient b K u x = 0 := by
  apply (ae_restrict_iff' hK.measurableSet.compl).mp
  have hcomponents : ∀ᵐ x ∂(volume : Measure E).restrict Kᶜ,
      ∀ i, (SobolevInv.CM.Construction.supportedH1Gradient b K u i) x = 0 :=
    ae_all_iff.mpr (supportedH1Gradient_support b hK u)
  filter_upwards [hcomponents, ae_restrict_of_ae
    (LpComponents.CM.Construction.lpOrthonormalSynthesis_coe (EuclideanSpace.basisFun ι ℂ) (SobolevInv.CM.Construction.supportedH1Gradient b K u))]
    with x hx hsynth
  change LpComponents.CM.Construction.lpOrthonormalSynthesis (EuclideanSpace.basisFun ι ℂ) (SobolevInv.CM.Construction.supportedH1Gradient b K u) x = 0
  rw [hsynth]
  simp only [hx, zero_smul, Finset.sum_const_zero]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GradientSupport.CM.Construction
