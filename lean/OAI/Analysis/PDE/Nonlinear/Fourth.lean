import OAI.Analysis.PDE.Nonlinear.IndexedLinear
import OAI.Analysis.PDE.Nonlinear.CoefficientJet

/-! The second nonlinear regularity upgrade for the actual Moore equation. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Green

local instance fourthFirstGroup (n : ℕ) : NormedAddCommGroup (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance fourthFirstSpace (n : ℕ) : NormedSpace ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance fourthSecondGroup (n : ℕ) :
    NormedAddCommGroup (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance fourthSecondSpace (n : ℕ) :
    NormedSpace ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ℝ) := inferInstance
local instance fourthMatrixDGroup (n : ℕ) :
    NormedAddCommGroup (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) :=
  inferInstanceAs (NormedAddCommGroup (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ((Fin n × Fin 4) → (Fin n × Fin 4) → ℝ)))
local instance fourthMatrixDSpace (n : ℕ) :
    NormedSpace ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) :=
  inferInstanceAs (NormedSpace ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] ((Fin n × Fin 4) → (Fin n × Fin 4) → ℝ)))

theorem moore_directional_C3At {n : ℕ} (hn : 3 ≤ n * 4) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ)
    (hu : ContDiff ℝ 3 u) (hf : ContDiff ℝ 3 f) (v x₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
    (hPDE : ∀ᶠ x in 𝓝 x₀, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x)
    (hPD : ∀ᶠ x in 𝓝 x₀, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)).PosDef) :
    ContDiffAt ℝ 3 (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) x₀ := by
  obtain ⟨g, hg, hge, A, DA, hA, hDA⟩ := exists_moore_coefficient_jet hn hα hα1 u f hu
    (hf.of_le (by norm_num)) x₀ hPDE hPD
  have hw : ContDiff ℝ 2 (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) := OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (by norm_num) v
  have hd : ContDiff ℝ 2 (OAI.Analysis.PDE.Dirichlet.directionalDerivative f v) := OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hf (by norm_num) v
  have hDg : HasLocalHolderBound α (fderiv ℝ g) x₀ := by
    let : NormedAddCommGroup (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) :=
      coefficientJetMatrixDGroup n
    let : NormedSpace ℝ (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ) :=
      coefficientJetMatrixDSpace n
    refine ⟨1, by norm_num, ‖DA‖ + 1, by positivity, ?_⟩
    intro x _ y _
    rw [← hDA x, ← hDA y]
    have hb : ‖OAI.Analysis.Normed.Function.Holder.HolderMap.value DA x - OAI.Analysis.Normed.Function.Holder.HolderMap.value DA y‖ ≤ ‖DA‖ * dist x y ^ α := by
      simpa only using! (@OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
        (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 →L[ℝ] Matrix (Fin n × Fin 4) (Fin n × Fin 4) ℝ)
        inferInstance (coefficientJetMatrixDGroup n) (coefficientJetMatrixDSpace n) α DA x y)
    apply hb.trans
    rw [dist_eq_norm]
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
  have hHw : HasLocalHolderBound α (fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v))) x₀ :=
    moore_directional_hessian_holder hn hα hα1 u f hu (hf.of_le (by norm_num)) v x₀ hPDE hPD
  have hDd : HasLocalHolderBound α (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative f v)) x₀ :=
    localHolderBound_of_C1At (hd.fderiv_right (m := 1) (by norm_num)).contDiffAt hα.le hα1.le
  have hAP : ∀ᶠ x in 𝓝 x₀, (g x).PosDef := by
    filter_upwards [hge, hPD] with x hx hy
    rw [hx]
    exact OAI.Analysis.PDE.Dirichlet.mooreRealMatrix_posDef _ hy
  have heq : (fun x => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)) =ᶠ[𝓝 x₀] f := hPDE
  have hEq : ∀ᶠ x in 𝓝 x₀,
      OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator g (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) x = OAI.Analysis.PDE.Dirichlet.directionalDerivative f v x := by
    filter_upwards [hge, heq.eventuallyEq_nhds] with x hx hy
    change (∑ i, ∑ j, g x i j * _) = _
    rw [hx]
    change OAI.Analysis.PDE.Dirichlet.indexedNondivergenceOperator (fun x => OAI.Analysis.PDE.Dirichlet.mooreRealMatrix (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x))
      (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) x = _
    rw [OAI.Analysis.PDE.Dirichlet.mooreRealMatrix_linearization_at _ hw.contDiffAt]
    exact OAI.Analysis.PDE.Dirichlet.mooreLinearization_directional_eq hu v (hf.differentiable (by norm_num) x) hy
  exact indexed_linear_C3At finProdFinEquiv hn hα hα1 g (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v)
    (OAI.Analysis.PDE.Dirichlet.directionalDerivative f v) x₀ hg hw (hd.of_le (by norm_num)) hDg hHw hDd hAP hEq

theorem moore_C4On_of_C3 {n : ℕ} (hn : 3 ≤ n * 4)
    (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ) (hu : ContDiff ℝ 3 u) (hf : ContDiff ℝ 3 f)
    {Ω : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)} (hΩ : IsOpen Ω)
    (hPDE : ∀ x ∈ Ω, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x)
    (hPD : ∀ x ∈ Ω, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)).PosDef) :
    ContDiffOn ℝ 4 u Ω := by
  change ContDiffOn ℝ ((3 : WithTop ℕ∞) + 1) u Ω
  apply contDiffOn_succ_of_fderiv_apply (hu.differentiable (by norm_num)).differentiableOn
    (by intro he; norm_num at he)
  intro v
  have hh : ContDiffOn ℝ 3 (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v) Ω := by
    intro x hx
    apply (moore_directional_C3At hn (α := 1 / 2) (by norm_num) (by norm_num)
      u f hu hf v x ?_ ?_).contDiffWithinAt
    · filter_upwards [hΩ.mem_nhds hx] with y hy
      exact hPDE y hy
    · filter_upwards [hΩ.mem_nhds hx] with y hy
      exact hPD y hy
  apply hh.congr
  intro x hx
  rw [fderivWithin_of_isOpen hΩ hx]
  rfl

theorem moore_C4At_of_C3At {n : ℕ} (hn : 3 ≤ n * 4)
    (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ) (x₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
    (hu : ContDiffAt ℝ 3 u x₀) (hf : ContDiffAt ℝ 3 f x₀)
    (hPDE : ∀ᶠ x in 𝓝 x₀, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x)
    (hPD : ∀ᶠ x in 𝓝 x₀, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)).PosDef) :
    ContDiffAt ℝ 4 u x₀ := by
  obtain ⟨g, hg, hgu⟩ := OAI.Analysis.PDE.Dirichlet.exists_contDiff_extension_near_point hu
  obtain ⟨d, hd, hdf⟩ := OAI.Analysis.PDE.Dirichlet.exists_contDiff_extension_near_point hf
  have hHg : ∀ᶠ x in 𝓝 x₀, OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x = OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x := by
    filter_upwards [hgu.eventuallyEq_nhds] with x hx
    exact OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.fourSlots hx
  have hp : ∀ᶠ x in 𝓝 x₀, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x) = d x ∧
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x)).PosDef := by
    filter_upwards [hHg, hdf, hPDE, hPD] with x hx hy hz hw
    rw [hx, hy]
    exact ⟨hz, hw⟩
  obtain ⟨r, hr, hh⟩ := Metric.eventually_nhds_iff.mp hp
  have hc := moore_C4On_of_C3 hn g d hg hd isOpen_ball
    (fun x hx => (hh hx).1) (fun x hx => (hh hx).2)
  exact ((hc x₀ (mem_ball_self hr)).contDiffAt (ball_mem_nhds x₀ hr)).congr_of_eventuallyEq hgu.symm

theorem moore_C4On_of_C3On {n : ℕ} (hn : 3 ≤ n * 4)
    (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ) {Ω : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)} (hΩ : IsOpen Ω)
    (hu : ContDiffOn ℝ 3 u Ω) (hf : ContDiffOn ℝ 3 f Ω)
    (hPDE : ∀ x ∈ Ω, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x)
    (hPD : ∀ x ∈ Ω, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)).PosDef) :
    ContDiffOn ℝ 4 u Ω := by
  intro x hx
  apply (moore_C4At_of_C3At hn u f x ((hu x hx).contDiffAt (hΩ.mem_nhds hx))
    ((hf x hx).contDiffAt (hΩ.mem_nhds hx)) ?_ ?_).contDiffWithinAt
  · filter_upwards [hΩ.mem_nhds hx] with y hy
    exact hPDE y hy
  · filter_upwards [hΩ.mem_nhds hx] with y hy
    exact hPD y hy

end OAI.Analysis.PDE.Nonlinear
