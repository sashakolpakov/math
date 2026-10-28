import OAI.Analysis.Calculus.Quaternion.IndexedCofactor
import OAI.Analysis.Calculus.Quaternion.Bochner

/-! Bochner averaging preserves the actual current's algebraic constraints. -/

noncomputable section
namespace OAI.Analysis.Calculus.Quaternion

open _root_.MeasureTheory OAI.LinearAlgebra.Moore
open scoped Matrix Matrix.Norms.Elementwise ComplexOrder Topology

variable {ι α : Type*} [Fintype ι] [MeasurableSpace α]

local instance : NormedAddCommGroup (Matrix ι ι Q) :=
  inferInstanceAs (NormedAddCommGroup (ι → ι → Q))

local instance : NormedSpace ℝ (Matrix ι ι Q) :=
  inferInstanceAs (NormedSpace ℝ (ι → ι → Q))

local instance : ContinuousSMul ℝ (Matrix ι ι Q) :=
  inferInstanceAs (ContinuousSMul ℝ (ι → ι → Q))

local instance : ContinuousENorm (Matrix ι ι Q) :=
  inferInstanceAs (ContinuousENorm (ι → ι → Q))

def currentRowCLM (r v : ι → Q) : Matrix ι ι Q →L[ℝ] Q :=
  ({ toFun := fun A => r ⬝ᵥ (A *ᵥ v)
     map_add' := by intros; simp [Matrix.add_mulVec, dotProduct_add]
     map_smul' := by intros; simp [Matrix.smul_mulVec, dotProduct_smul] } :
    Matrix ι ι Q →ₗ[ℝ] Q).toContinuousLinearMap

def currentQuadraticCLM (v : ι → Q) : Matrix ι ι Q →L[ℝ] ℝ :=
  ({ toFun := fun A => (star v ⬝ᵥ (A *ᵥ v)).re
     map_add' := by intros; simp [Matrix.add_mulVec, dotProduct_add]
     map_smul' := by intros; simp [Matrix.smul_mulVec, dotProduct_smul] } :
    Matrix ι ι Q →ₗ[ℝ] ℝ).toContinuousLinearMap

def currentStarCLM : Matrix ι ι Q →L[ℝ] Matrix ι ι Q :=
  ({ toFun := Matrix.conjTranspose
     map_add' := Matrix.conjTranspose_add
     map_smul' := by
       intro c A
       apply Matrix.ext
       intro i j
       simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, Quaternion.star_smul,
         RingHom.id_apply] } : Matrix ι ι Q →ₗ[ℝ] Matrix ι ι Q).toContinuousLinearMap

theorem integral_current_isHermitian {μ : Measure α} {A : α → Matrix ι ι Q}
    (hA : Integrable A μ) (hH : ∀ᵐ x ∂μ, (A x).IsHermitian) :
    (∫ x, A x ∂μ).IsHermitian := by
  change currentStarCLM (∫ x, A x ∂μ) = ∫ x, A x ∂μ
  have hc : currentStarCLM (∫ x, A x ∂μ) = ∫ x, currentStarCLM (A x) ∂μ := by
    simpa only using! (currentStarCLM.integral_comp_comm hA).symm
  rw [hc]
  exact integral_congr_ae hH

theorem integral_current_row_zero {μ : Measure α} {A : α → Matrix ι ι Q}
    (hA : Integrable A μ) (r v : ι → Q)
    (hzero : ∀ᵐ x ∂μ, r ⬝ᵥ (A x *ᵥ v) = 0) :
    r ⬝ᵥ ((∫ x, A x ∂μ) *ᵥ v) = 0 := by
  change currentRowCLM r v (∫ x, A x ∂μ) = 0
  have hc : currentRowCLM r v (∫ x, A x ∂μ) = ∫ x, currentRowCLM r v (A x) ∂μ := by
    simpa only using! ((currentRowCLM r v).integral_comp_comm hA).symm
  rw [hc]
  simpa using! integral_congr_ae hzero

theorem integral_current_quadratic_nonneg {μ : Measure α} {A : α → Matrix ι ι Q}
    (hA : Integrable A μ) (v : ι → Q)
    (hpos : ∀ᵐ x ∂μ, 0 ≤ (star v ⬝ᵥ (A x *ᵥ v)).re) :
    0 ≤ (star v ⬝ᵥ ((∫ x, A x ∂μ) *ᵥ v)).re := by
  change 0 ≤ currentQuadraticCLM v (∫ x, A x ∂μ)
  have hc : currentQuadraticCLM v (∫ x, A x ∂μ) = ∫ x, currentQuadraticCLM v (A x) ∂μ := by
    simpa only using! ((currentQuadraticCLM v).integral_comp_comm hA).symm
  rw [hc]
  exact integral_nonneg_of_ae hpos

theorem integral_current_posSemidef {μ : Measure α} {A : α → Matrix ι ι Q}
    (hA : Integrable A μ) (hpos : ∀ᵐ x ∂μ, (OAI.LinearAlgebra.Moore.complexify (A x)).PosSemidef) :
    (OAI.LinearAlgebra.Moore.complexify (∫ x, A x ∂μ)).PosSemidef := by
  have hH : ∀ᵐ x ∂μ, (A x).IsHermitian := by
    apply hpos.mono
    intro x hx
    apply OAI.LinearAlgebra.Moore.complexify_injective
    rw [OAI.LinearAlgebra.Moore.complexify_star]
    exact hx.isHermitian
  apply (indexed_complexify_posSemidef_iff _ (integral_current_isHermitian hA hH)).mpr
  intro v
  apply integral_current_quadratic_nonneg hA v
  filter_upwards [hpos, hH] with x hx hh
  exact (indexed_complexify_posSemidef_iff _ hh).mp hx v

variable {E σ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype σ]

def currentDivergenceCLM (e : σ → Q) (d : ι × σ → E) (b : ι) :
    (E →L[ℝ] Matrix ι ι Q) →L[ℝ] Q :=
  ({ toFun := fun L => strongDivergence e (fun p => L (d p)) b
     map_add' := by
       intros
       simp [strongDivergence, mul_add, Finset.sum_add_distrib]
     map_smul' := by
       intros
       simp [strongDivergence, Finset.smul_sum] } :
    (E →L[ℝ] Matrix ι ι Q) →ₗ[ℝ] Q).toContinuousLinearMap

/-- Differentiation and averaging preserve conservation under the usual local
dominated-differentiation hypotheses. All derivatives here are actual Fréchet derivatives. -/
theorem integral_current_divergence_zero
    {μ : Measure α} (A : E → α → Matrix ι ι Q) {x : E} {s : Set E} (hs : s ∈ 𝓝 x)
    (bound : α → ℝ) (hbound : Integrable bound μ)
    (hmeas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (A y) μ) (hA : Integrable (A x) μ)
    (hDmeas : AEStronglyMeasurable (fun t => fderiv ℝ (fun y => A y t) x) μ)
    (hD : ∀ᵐ t ∂μ, ∀ y ∈ s, DifferentiableAt ℝ (fun z => A z t) y)
    (hDbound : ∀ᵐ t ∂μ, ∀ y ∈ s,
      ‖(fderiv ℝ (fun z => A z t) y : E →L[ℝ] (ι → ι → Q))‖ ≤ bound t)
    (e : σ → Q) (d : ι × σ → E) (b : ι)
    (hzero : ∀ᵐ t ∂μ, strongDivergence e
      (fun p => fderiv ℝ (fun y => A y t) x (d p)) b = 0) :
    strongDivergence e (fun p => fderiv ℝ (fun y => ∫ t, A y t ∂μ) x (d p)) b = 0 := by
  change currentDivergenceCLM e d b (fderiv ℝ (fun y => ∫ t, A y t ∂μ) x) = 0
  simpa only using! integral_fderiv_linear_zero A hs bound hbound hmeas hA hDmeas hD hDbound
    (currentDivergenceCLM e d b) hzero

end OAI.Analysis.Calculus.Quaternion
