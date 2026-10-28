import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpComponents

/-! # Finite Lp -/

namespace OAI.Analysis.HodgeTheory.Decomposition.FiniteLp.Constructions

noncomputable section

/-! Finite families of vector-valued L² functions as actual L² functions
with values in the Hilbert direct sum. -/

open _root_.MeasureTheory

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpComponents.CM.Construction

variable {α 𝕜 F ι : Type*} [MeasurableSpace α] [RCLike 𝕜]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [Fintype ι] {μ : Measure α}

def finiteHilbertSingle [DecidableEq ι] (i : ι) : F →L[𝕜] PiLp 2 (fun _ : ι => F) :=
  (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single 𝕜 (fun _ : ι => F) i)

omit [Fintype ι] in
theorem finiteHilbertSingle_apply [DecidableEq ι] (i : ι) (v : F) :
    finiteHilbertSingle (𝕜 := 𝕜) i v = PiLp.single 2 i v := rfl

def finiteLpSynthesis : PiLp 2 (fun _ : ι => Lp F 2 μ) →L[𝕜] Lp (PiLp 2 (fun _ : ι => F)) 2 μ := by
  classical
  exact ∑ i, ((finiteHilbertSingle (𝕜 := 𝕜) (F := F) i).compLpL 2 μ).comp
    ((ContinuousLinearMap.proj i).comp
      (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => Lp F 2 μ)).toContinuousLinearMap)

theorem finiteLpSynthesis_coe (u : PiLp 2 (fun _ : ι => Lp F 2 μ)) :
    ∀ᵐ x ∂μ, finiteLpSynthesis (𝕜 := 𝕜) (F := F) (ι := ι) (μ := μ) u x = WithLp.toLp 2 (fun i => u i x) := by
  classical
  have hcoe : ∀ᵐ x ∂μ, ∀ i : ι,
      ((finiteHilbertSingle (𝕜 := 𝕜) (F := F) i).compLpL 2 μ (u i)) x =
        PiLp.single 2 i (u i x) :=
    ae_all_iff.mpr (fun i => by
      have h := (finiteHilbertSingle (𝕜 := 𝕜) i).coeFn_compLpL (u i)
      filter_upwards [h] with x hx
      exact hx.trans (finiteHilbertSingle_apply i (u i x)))
  have hsum := AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpComponents.CM.Construction.lp_coe_finsetSum (fun i =>
    (finiteHilbertSingle (𝕜 := 𝕜) (F := F) i).compLpL 2 μ (u i)) Finset.univ
  filter_upwards [hcoe, hsum] with x hx hsumx
  simp only [finiteLpSynthesis, sum_apply, ContinuousLinearMap.comp_apply]
  change (∑ i, (finiteHilbertSingle (𝕜 := 𝕜) i).compLpL 2 μ (u i)) x = _
  rw [hsumx]
  simp only [hx]
  apply PiLp.ext
  intro i
  simp

theorem finiteLpSynthesis_inner (u v : PiLp 2 (fun _ : ι => Lp F 2 μ)) :
    inner 𝕜 (finiteLpSynthesis (𝕜 := 𝕜) (F := F) (ι := ι) (μ := μ) u) (finiteLpSynthesis (𝕜 := 𝕜) (F := F) (ι := ι) (μ := μ) v) = inner 𝕜 u v := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, ∑ i, inner 𝕜 (u i x) (v i x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [finiteLpSynthesis_coe (𝕜 := 𝕜) u, finiteLpSynthesis_coe (𝕜 := 𝕜) v]
        with x hx hy
      rw [hx, hy]
      rfl
    _ = ∑ i, inner 𝕜 (u i) (v i) :=
      integral_finsetSum Finset.univ (fun i _ => L2.integrable_inner (𝕜 := 𝕜) (u i) (v i))
    _ = inner 𝕜 u v := rfl

theorem finiteLpSynthesis_norm (u : PiLp 2 (fun _ : ι => Lp F 2 μ)) :
    ‖finiteLpSynthesis (𝕜 := 𝕜) (F := F) (ι := ι) (μ := μ) u‖ = ‖u‖ := by
  have h := congrArg RCLike.re (finiteLpSynthesis_inner (𝕜 := 𝕜) u u)
  rw [← norm_sq_eq_re_inner, ← norm_sq_eq_re_inner] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

end

end OAI.Analysis.HodgeTheory.Decomposition.FiniteLp.Constructions
