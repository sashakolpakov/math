import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpCoefficients
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Lp Components -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpComponents.CM.Construction

noncomputable section

section

/-! Finite orthonormal synthesis identifies componentwise L2 vector fields
with actual vector-valued L2 functions, preserving their inner product. -/

open _root_.MeasureTheory
open scoped ComplexConjugate

variable {α 𝕜 E ι : Type*} [MeasurableSpace α] [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [Fintype ι] {μ : Measure α}

omit [RCLike 𝕜] [InnerProductSpace 𝕜 E] [Fintype ι] in
theorem lp_coe_finsetSum (u : ι → Lp E 2 μ) (s : Finset ι) :
    ∀ᵐ x ∂μ, (∑ i ∈ s, u i) x = ∑ i ∈ s, u i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero E 2 μ] with x hx
    exact hx
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (u i) (∑ j ∈ s, u j), ih] with x hx hy
    simp only [hx, Pi.add_apply, hy]

def lpOrthonormalSynthesis (b : OrthonormalBasis ι 𝕜 E) :
    PiLp 2 (fun _ : ι => Lp 𝕜 2 μ) →L[𝕜] Lp E 2 μ :=
  ∑ i, (((ContinuousLinearMap.id 𝕜 𝕜).smulRight (b i)).compLpL 2 μ).comp
    ((ContinuousLinearMap.proj i).comp
      (PiLp.continuousLinearEquiv 2 𝕜 (fun _ : ι => Lp 𝕜 2 μ)).toContinuousLinearMap)

theorem lpOrthonormalSynthesis_coe (b : OrthonormalBasis ι 𝕜 E)
    (u : PiLp 2 (fun _ : ι => Lp 𝕜 2 μ)) :
    ∀ᵐ x ∂μ, lpOrthonormalSynthesis b u x = ∑ i, u i x • b i := by
  have hcoe : ∀ᵐ x ∂μ, ∀ i : ι,
      (((ContinuousLinearMap.id 𝕜 𝕜).smulRight (b i)).compLpL 2 μ (u i)) x = u i x • b i :=
    ae_all_iff.mpr (fun i => ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (b i)).coeFn_compLpL (u i))
  have hsum := lp_coe_finsetSum (fun i =>
    ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (b i)).compLpL 2 μ (u i)) Finset.univ
  filter_upwards [hcoe, hsum] with x hx hsumx
  simp only [lpOrthonormalSynthesis, sum_apply, ContinuousLinearMap.comp_apply]
  change (∑ i, ((ContinuousLinearMap.id 𝕜 𝕜).smulRight (b i)).compLpL 2 μ (u i)) x = _
  rw [hsumx]
  simp only [hx]

theorem lpOrthonormalSynthesis_inner (b : OrthonormalBasis ι 𝕜 E)
    (u v : PiLp 2 (fun _ : ι => Lp 𝕜 2 μ)) :
    inner 𝕜 (lpOrthonormalSynthesis b u) (lpOrthonormalSynthesis b v) = inner 𝕜 u v := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, ∑ i, inner 𝕜 (u i x) (v i x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [lpOrthonormalSynthesis_coe b u, lpOrthonormalSynthesis_coe b v] with x hx hy
      rw [hx, hy, b.orthonormal.inner_sum]
      simp only [RCLike.inner_apply, mul_comm]
    _ = ∑ i, inner 𝕜 (u i) (v i) :=
      integral_finsetSum Finset.univ (fun i _ => L2.integrable_inner (𝕜 := 𝕜) (u i) (v i))
    _ = inner 𝕜 u v := rfl

def lpOrthonormalSynthesisIsometry (b : OrthonormalBasis ι 𝕜 E) :
    PiLp 2 (fun _ : ι => Lp 𝕜 2 μ) →ₗᵢ[𝕜] Lp E 2 μ :=
  { (lpOrthonormalSynthesis b).toLinearMap with
    norm_map' := fun u => by
      have h := congrArg RCLike.re (lpOrthonormalSynthesis_inner b u u)
      rw [← norm_sq_eq_re_inner, ← norm_sq_eq_re_inner] at h
      exact (sq_eq_sq₀ (norm_nonneg (lpOrthonormalSynthesis b u)) (norm_nonneg u)).mp h }

end

/-! Actual component projections of complex L2 vector fields detect zero. -/

open _root_.MeasureTheory Filter

variable {ι α : Type*} [Fintype ι] [MeasurableSpace α] (μ : Measure α)

def complexVectorCoordinate (i : ι) : EuclideanSpace ℂ ι →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp (PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => ℂ)).toContinuousLinearMap

def complexLpComponent (i : ι) : Lp (EuclideanSpace ℂ ι) 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (complexVectorCoordinate i).compLpL 2 μ

theorem complexLpComponent_coe (i : ι) (u : Lp (EuclideanSpace ℂ ι) 2 μ) :
    complexLpComponent μ i u =ᵐ[μ] fun x => u x i :=
  (complexVectorCoordinate i).coeFn_compLpL u

theorem complexLpComponent_eq_zero (u : Lp (EuclideanSpace ℂ ι) 2 μ)
    (hu : ∀ i, complexLpComponent μ i u = 0) : u = 0 := by
  have hall : ∀ᵐ x ∂μ, ∀ i : ι, u x i = 0 := by
    apply ae_all_iff.mpr
    intro i
    have hi := complexLpComponent_coe μ i u
    rw [hu i] at hi
    filter_upwards [hi, Lp.coeFn_zero ℂ 2 μ] with x hx hzero
    exact hx.symm.trans hzero
  apply Lp.ext
  filter_upwards [hall, Lp.coeFn_zero (EuclideanSpace ℂ ι) 2 μ] with x hx hzero
  rw [hzero]
  apply PiLp.ext
  intro i
  exact hx i

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LpComponents.CM.Construction
