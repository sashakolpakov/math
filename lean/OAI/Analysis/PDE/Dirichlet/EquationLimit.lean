import OAI.Analysis.PDE.Dirichlet.DerivativeLimit
import OAI.Analysis.PDE.Dirichlet.HessianMapNorm
import OAI.Analysis.PDE.Dirichlet.FixedData
import OAI.Analysis.PDE.Dirichlet.PositiveDeterminant

open Set Filter
open scoped Topology Matrix ComplexOrder
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem complex_posSemidef_of_tendsto {ι : Type*} [Fintype ι]
    {A : ℕ → Matrix ι ι ℂ} {B : Matrix ι ι ℂ}
    (h : Tendsto A atTop (𝓝 B)) (hpos : ∀ k, (A k).PosSemidef) : B.PosSemidef := by
  have hh : Continuous (fun M : Matrix ι ι ℂ ↦ Mᴴ) := by fun_prop
  have hherm : B.IsHermitian := by
    apply tendsto_nhds_unique (hh.continuousAt.tendsto.comp h)
    change Tendsto (fun k ↦ (A k)ᴴ) atTop (𝓝 B)
    have he (k) : (A k)ᴴ = A k := (hpos k).isHermitian
    simpa only [he] using h
  refine ⟨hherm, ?_⟩
  intro z
  have hz : Continuous (fun M : Matrix ι ι ℂ ↦
      z.sum fun i zi ↦ z.sum fun j zj ↦ star zi * M i j * zj) := by
    classical
    simp only [Finsupp.sum]
    fun_prop
  exact le_of_tendsto_of_tendsto tendsto_const_nhds (hz.continuousAt.tendsto.comp h)
    (Eventually.of_forall (fun k ↦ (hpos k).2 z))

theorem complexify_posSemidef_of_tendsto {n : ℕ}
    {A : ℕ → Matrix (Fin n) (Fin n) Q} {B : Matrix (Fin n) (Fin n) Q}
    (h : Tendsto A atTop (𝓝 B))
    (hpos : ∀ k, (OAI.LinearAlgebra.Moore.complexify (A k)).PosSemidef) : (OAI.LinearAlgebra.Moore.complexify B).PosSemidef := by
  have hc := (continuous_complexify_map
    (continuous_id : Continuous (fun A : Matrix (Fin n) (Fin n) Q ↦ A))).continuousAt.tendsto.comp h
  exact complex_posSemidef_of_tendsto hc hpos

theorem quaternionHessian_tendsto_of_second_derivative {n s : ℕ}
    (e : Fin s → Q) {u : ℕ → CoordinateSpace n s → ℝ}
    {v : CoordinateSpace n s → ℝ} {x : CoordinateSpace n s}
    (h : Tendsto (fun k ↦ fderiv ℝ (fderiv ℝ (u k)) x) atTop
      (𝓝 (fderiv ℝ (fderiv ℝ v) x))) :
    Tendsto (fun k ↦ quaternionHessian e (u k) x) atTop (𝓝 (quaternionHessian e v x)) := by
  have hr : Tendsto (fun k ↦ realHessian (u k) x) atTop (𝓝 (realHessian v x)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    have hc : Continuous (fun T : CoordinateSpace n s →L[ℝ] CoordinateSpace n s →L[ℝ] ℝ ↦
        T (coordinateVector i) (coordinateVector j)) :=
      (continuous_id.clm_apply continuous_const).clm_apply continuous_const
    exact hc.continuousAt.tendsto.comp h
  exact (hessianMatrixCLM e).continuous.continuousAt.tendsto.comp hr

/-- The actual nonlinear equation and strict positivity survive a C² limit.
Positivity is not assumed of the limit: closedness gives semidefiniteness,
and the positive limiting density excludes singularity. -/
theorem moore_equation_posDef_of_second_derivative_limit {n : ℕ}
    {u : ℕ → CoordinateSpace n 4 → ℝ} {v : CoordinateSpace n 4 → ℝ}
    {x : CoordinateSpace n 4} {f : ℕ → ℝ} {g : ℝ}
    (h : Tendsto (fun k ↦ fderiv ℝ (fderiv ℝ (u k)) x) atTop
      (𝓝 (fderiv ℝ (fderiv ℝ v) x)))
    (hf : Tendsto f atTop (𝓝 g)) (hg : 0 < g)
    (heq : ∀ k, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u k) x) = f k)
    (hpos : ∀ k, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u k) x)).PosDef) :
    OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots v x) = g ∧
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots v x)).PosDef := by
  have hA := quaternionHessian_tendsto_of_second_derivative OAI.Analysis.Calculus.Quaternion.fourSlots h
  have hd := (OAI.LinearAlgebra.Moore.continuous_mooreDet n).continuousAt.tendsto.comp hA
  have heq' : OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots v x) = g := by
    apply tendsto_nhds_unique hd
    change Tendsto (fun k ↦ OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u k) x)) atTop (𝓝 g)
    simpa only [heq] using hf
  have hsem := complexify_posSemidef_of_tendsto hA (fun k ↦ (hpos k).posSemidef)
  exact ⟨heq', complexify_posDef_of_posSemidef_mooreDet_pos _ hsem (by rwa [heq'])⟩

/-- Closedness of the equation for locally uniform limits of the first two
derivatives. This is independent of the subsequent regularity bootstrapping. -/
theorem local_moore_equation_limit {n : ℕ} {Ω : Set (CoordinateSpace n 4)}
    (hΩ : IsOpen Ω) {u : ℕ → CoordinateSpace n 4 → ℝ} {v : CoordinateSpace n 4 → ℝ}
    {G : CoordinateSpace n 4 → CoordinateSpace n 4 →L[ℝ] ℝ}
    {H : CoordinateSpace n 4 → CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4 →L[ℝ] ℝ}
    {F : ℕ → CoordinateSpace n 4 → ℝ} {g : CoordinateSpace n 4 → ℝ}
    (hu : ∀ k, ContDiff ℝ 2 (u k))
    (hv : ∀ x ∈ Ω, Tendsto (fun k ↦ u k x) atTop (𝓝 (v x)))
    (hG : TendstoLocallyUniformlyOn (fun k ↦ fderiv ℝ (u k)) G atTop Ω)
    (hH : TendstoLocallyUniformlyOn (fun k ↦ fderiv ℝ (fderiv ℝ (u k))) H atTop Ω)
    (hF : ∀ x ∈ Ω, Tendsto (fun k ↦ F k x) atTop (𝓝 (g x)))
    (hg : ∀ x ∈ Ω, 0 < g x)
    (heq : ∀ k x, x ∈ Ω → OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u k) x) = F k x)
    (hpos : ∀ k x, x ∈ Ω → (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (u k) x)).PosDef) :
    ∀ x ∈ Ω, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots v x) = g x ∧
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots v x)).PosDef := by
  have hder := second_fderiv_of_locally_uniform_limit hΩ hu hv hG hH
  intro x hx
  apply moore_equation_posDef_of_second_derivative_limit
    (by rw [(hder x hx).2]; exact hH.tendsto_at hx)
    (hF x hx) (hg x hx) (fun k ↦ heq k x hx) (fun k ↦ hpos k x hx)

end OAI.Analysis.PDE.Dirichlet
