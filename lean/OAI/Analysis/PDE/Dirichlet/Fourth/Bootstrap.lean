import OAI.Analysis.PDE.Dirichlet.Fourth.Equation
import OAI.Analysis.PDE.Nonlinear.BanachBootstrap

/-! Fourth-order Hölder regularity obtained from the equation, without a
fifth derivative or an assumed fourth-order Hölder bound. -/

noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.Elementwise ComplexOrder
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Nonlinear OAI.LinearAlgebra.Moore OAI.Analysis.Normed.Function.Holder

local instance fourthBootstrapFirstGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthBootstrapFirstSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthBootstrapSecondGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthBootstrapSecondSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthBootstrapThirdGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthBootstrapThirdSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthBootstrapFourthGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthBootstrapFourthSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem moore_second_directional_hessian_holder {n : ℕ} (hn : 3 ≤ n * 4) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (u f : CoordinateSpace n 4 → ℝ)
    (hu : ContDiff ℝ 4 u) (hf : ContDiff ℝ 3 f) (v w x₀ : CoordinateSpace n 4)
    (hPDE : ∀ᶠ x in 𝓝 x₀, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x)
    (hPD : ∀ᶠ x in 𝓝 x₀, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)).PosDef) :
    OAI.Analysis.PDE.Nonlinear.HasLocalHolderBound α
      (fderiv ℝ (fderiv ℝ (directionalDerivative (directionalDerivative u v) w))) x₀ := by
  let A := fun y => mooreRealMatrix (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u y)
  have hA : ContDiff ℝ 1 A :=
    (contDiff_mooreRealMatrix n 1).comp
      (OAI.Analysis.PDE.Green.contDiff_quaternionHessian_one OAI.Analysis.Calculus.Quaternion.fourSlots (hu.of_le (by norm_num)))
  have hv : ContDiff ℝ 3 (directionalDerivative u v) :=
    contDiff_directionalDerivative hu (by norm_num) v
  have hvw : ContDiff ℝ 2 (directionalDerivative (directionalDerivative u v) w) :=
    contDiff_directionalDerivative hv (by norm_num) w
  have hAP : ∀ᶠ x in 𝓝 x₀, (A x).PosDef := by
    filter_upwards [hPD] with x hx
    exact mooreRealMatrix_posDef _ hx
  have heq : (fun x => OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)) =ᶠ[𝓝 x₀] f := hPDE
  have hEq : ∀ᶠ x in 𝓝 x₀, indexedNondivergenceOperator A
      (directionalDerivative (directionalDerivative u v) w) x = mooreSecondForcing u f v w x := by
    filter_upwards [heq.eventuallyEq_nhds] with x hx
    exact moore_second_directional_equation u f hu (hf.of_le (by norm_num)) v w x hx
  exact OAI.Analysis.PDE.Nonlinear.indexed_C1_coefficient_schauder finProdFinEquiv hn hα hα1 A
    (directionalDerivative (directionalDerivative u v) w) (mooreSecondForcing u f v w) x₀
    hA.contDiffAt hvw (contDiff_mooreSecondForcing u f hu hf v w).contDiffAt hAP hEq

theorem fourth_derivative_directional_hessian {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (hu : ContDiff ℝ 4 u) (x v w : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) x v w =
      fderiv ℝ (fderiv ℝ (directionalDerivative (directionalDerivative u w) v)) x := by
  have h3 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) :=
    ((hu.fderiv_right (m := 3) (by norm_num)).fderiv_right
      (m := 2) (by norm_num)).fderiv_right (by norm_num)
  have he : (fun y => fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y w) =
      fderiv ℝ (fderiv ℝ (directionalDerivative u w)) := by
    funext y
    exact OAI.Analysis.PDE.Nonlinear.third_derivative_directional_hessian u (hu.of_le (by norm_num)) y w
  have hd := congrArg (fun f => fderiv ℝ f x v) he
  rw [fderiv_clm_apply (h3.differentiable one_ne_zero x) (differentiableAt_const w)] at hd
  rw [OAI.Analysis.PDE.Nonlinear.third_derivative_directional_hessian (directionalDerivative u w)
    (contDiff_directionalDerivative hu (by norm_num) w)] at hd
  simpa using hd

theorem moore_fourth_derivative_holder {n : ℕ} (hn : 3 ≤ n * 4) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (u f : CoordinateSpace n 4 → ℝ)
    (hu : ContDiff ℝ 4 u) (hf : ContDiff ℝ 3 f) (x₀ : CoordinateSpace n 4)
    (hPDE : ∀ᶠ x in 𝓝 x₀, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x)
    (hPD : ∀ᶠ x in 𝓝 x₀, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)).PosDef) :
    OAI.Analysis.PDE.Nonlinear.HasLocalHolderBound α (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u)))) x₀ := by
  let : NeZero n := ⟨by omega⟩
  let b := EuclideanSpace.basisFun (Fin n × Fin 4) ℝ
  apply OAI.Analysis.PDE.Nonlinear.locally_holder_of_basis_components b
  intro i
  apply OAI.Analysis.PDE.Nonlinear.locally_holder_of_basis_components b
  intro j
  obtain ⟨r, hr, C, hC, hh⟩ := moore_second_directional_hessian_holder hn hα hα1 u f hu hf
    (b j) (b i) x₀ hPDE hPD
  refine ⟨r, hr, C, hC, ?_⟩
  intro x hx y hy
  simpa only [fourth_derivative_directional_hessian u hu] using hh x hx y hy

theorem moore_fourth_derivative_holder_local {n : ℕ} (hn : 3 ≤ n * 4) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (u f : CoordinateSpace n 4 → ℝ)
    (x₀ : CoordinateSpace n 4) (hu : ContDiffAt ℝ 4 u x₀) (hf : ContDiffAt ℝ 3 f x₀)
    (hPDE : ∀ᶠ x in 𝓝 x₀, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x)
    (hPD : ∀ᶠ x in 𝓝 x₀, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)).PosDef) :
    OAI.Analysis.PDE.Nonlinear.HasLocalHolderBound α (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u)))) x₀ := by
  obtain ⟨g, hg, hgu⟩ := exists_contDiff_extension_near_point hu
  obtain ⟨d, hd, hdf⟩ := exists_contDiff_extension_near_point hf
  have hHg : ∀ᶠ x in 𝓝 x₀, quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x = quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x := by
    filter_upwards [hgu.eventuallyEq_nhds] with x hx
    exact quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.fourSlots hx
  have hp : ∀ᶠ x in 𝓝 x₀, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x) = d x := by
    filter_upwards [hHg, hdf, hPDE] with x hx hy hz
    rw [hx, hz, hy]
  have hpos : ∀ᶠ x in 𝓝 x₀, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x)).PosDef := by
    filter_upwards [hHg, hPD] with x hx hy
    rwa [hx]
  obtain ⟨r, hr, C, hC, hh⟩ := moore_fourth_derivative_holder hn hα hα1 g d hg hd x₀ hp hpos
  obtain ⟨s, hs, hsame⟩ := Metric.eventually_nhds_iff.mp
    ((((hgu.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ))
  refine ⟨min r s, lt_min hr hs, C, hC, ?_⟩
  intro x hx y hy
  rw [← hsame (ball_subset_ball (min_le_right r s) hx),
    ← hsame (ball_subset_ball (min_le_right r s) hy)]
  exact hh x (ball_subset_ball (min_le_left r s) hx) y (ball_subset_ball (min_le_left r s) hy)

/-- A genuine rough C²,α jet solving the positive Moore equation has
interior C⁴ regularity. No higher jet is part of the input. -/
theorem moore_C4_of_banach_jet {n : ℕ} (hn : 3 ≤ n * 4) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    {Ω K : Set (CoordinateSpace n 4)} (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K)
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) (f : CoordinateSpace n 4 → ℝ)
    (hf : ContDiffOn ℝ 3 f Ω)
    (hPDE : ∀ x ∈ Ω, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.PDE.Nonlinear.banachJetFunction U) x) = f x)
    (hPD : ∀ x ∈ Ω, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.PDE.Nonlinear.banachJetFunction U) x)).PosDef) :
    ContDiffOn ℝ 4 (OAI.Analysis.PDE.Nonlinear.banachJetFunction U) Ω := by
  exact OAI.Analysis.PDE.Nonlinear.moore_C4On_of_C3On hn (OAI.Analysis.PDE.Nonlinear.banachJetFunction U) f hΩ
    (OAI.Analysis.PDE.Nonlinear.moore_C3_of_banach_jet hn hα hα1 hΩ hΩK U f (hf.of_le (by norm_num)) hPDE hPD)
    hf hPDE hPD

/-- The fourth derivative of that rough jet is locally Hölder. In particular,
this applies to the Banach implicit-function solutions before any global C⁴
representative has been constructed. -/
theorem moore_banach_jet_fourth_holder {n : ℕ} (hn : 3 ≤ n * 4) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1)
    {Ω K : Set (CoordinateSpace n 4)} (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K)
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) (f : CoordinateSpace n 4 → ℝ)
    (hf : ContDiffOn ℝ 3 f Ω)
    (hPDE : ∀ x ∈ Ω, OAI.LinearAlgebra.Moore.mooreDet n (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.PDE.Nonlinear.banachJetFunction U) x) = f x)
    (hPD : ∀ x ∈ Ω, (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (OAI.Analysis.PDE.Nonlinear.banachJetFunction U) x)).PosDef)
    {x : CoordinateSpace n 4} (hx : x ∈ Ω) :
    OAI.Analysis.PDE.Nonlinear.HasLocalHolderBound α
      (fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Nonlinear.banachJetFunction U))))) x := by
  apply moore_fourth_derivative_holder_local hn hα hα1 (OAI.Analysis.PDE.Nonlinear.banachJetFunction U) f x
    (((moore_C4_of_banach_jet hn hα hα1 hΩ hΩK U f hf hPDE hPD) x hx).contDiffAt
      (hΩ.mem_nhds hx)) ((hf x hx).contDiffAt (hΩ.mem_nhds hx))
  · filter_upwards [hΩ.mem_nhds hx] with y hy
    exact hPDE y hy
  · filter_upwards [hΩ.mem_nhds hx] with y hy
    exact hPD y hy

end OAI.Analysis.PDE.Dirichlet
