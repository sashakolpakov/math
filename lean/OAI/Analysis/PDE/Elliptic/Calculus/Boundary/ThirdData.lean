import OAI.Analysis.PDE.Elliptic.Calculus.Boundary.Solution
import OAI.Analysis.PDE.Elliptic.Calculus.Boundary.LowerJets
import OAI.Analysis.PDE.Elliptic.Calculus.Boundary.GlobalElliptic
import OAI.Analysis.PDE.Elliptic.Boundary.Third.NormSchauder

noncomputable section
open Set Filter Metric InnerProductSpace
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Schauder

variable {m n : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin m)
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4

/-- Verified inputs for the flat boundary estimate. In the nonlinear
application these are constructed from the undifferentiated equation. -/
structure FlatThirdEquation (k : Fin m) (K : Set X) (α ell Λ N B V : ℝ) (u : X → ℝ) where
  coefficient : OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix (Fin m) (Fin m) ℝ) α
  source : Fin m → OAI.Analysis.Normed.Function.Holder.HolderMap X ℝ α
  norm_coefficient : ‖coefficient‖ ≤ N
  norm_source : ∀ i, ‖source i‖ ≤ B
  positive : (OAI.Analysis.Normed.Function.Holder.HolderMap.value coefficient 0).PosDef
  lower : ∀ v, ell*‖v‖^2 ≤ inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (OAI.Analysis.Normed.Function.Holder.HolderMap.value coefficient 0) v)
  upper : ∀ v, inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (OAI.Analysis.Normed.Function.Holder.HolderMap.value coefficient 0) v) ≤ Λ*‖v‖^2
  diagonal : ∀ x ∈ ball 0 (1/8), 0 ≤ x k → ell ≤ OAI.Analysis.Normed.Function.Holder.HolderMap.value coefficient x k k
  trace : ∀ i, i ≠ k → ∀ x ∈ ball 0 (1/8), x k = 0 → OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1) x = 0
  first : ∀ x ∈ K, ‖fderiv ℝ u x‖ ≤ V
  second : ∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ V
  equation : ∀ i, ∀ x ∈ ball 0 (1/8), 0 < x k →
    OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value coefficient) (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1)) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value (source i) x

theorem isometry_chart_nondivergence_eq {Y : Type*} [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y] (e : X ≃ₗᵢ[ℝ] Y)
    (J A : X → Y →L[ℝ] Y) (b : X → Matrix (Fin m) (Fin m) ℝ)
    (u : X → ℝ) (hu : ContDiff ℝ 2 u) (x : X)
    (hA : (A x).toLinearMap.IsSymmetric)
    (hb : b x = OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix (OAI.Analysis.PDE.Dirichlet.isometryConjugate e (pullbackEllipticOperator (J x) (A x)))) :
    OAI.Analysis.PDE.Schauder.nondivergenceOperator b u x = ellipticTrace
      (fun z => OAI.Analysis.PDE.Dirichlet.isometryConjugate e (pullbackEllipticOperator (J z) (A z))) u x := by
  have hs : (OAI.Analysis.PDE.Dirichlet.isometryConjugate e (pullbackEllipticOperator (J x) (A x))).toLinearMap.IsSymmetric := by
    rw [OAI.Analysis.PDE.Dirichlet.isometryConjugate_pullback]
    exact OAI.Analysis.PDE.Schauder.pullback_coefficient_isSymmetric _ _ (OAI.Analysis.PDE.Dirichlet.isometryConjugate_isSymmetric e _ hA)
  have he := OAI.Analysis.PDE.Schauder.ellipticTrace_eq_nondivergenceOperator
    (fun z => OAI.Analysis.PDE.Dirichlet.isometryConjugate e (pullbackEllipticOperator (J z) (A z))) u hu x hs
  apply Eq.trans _ he.symm
  simp only [OAI.Analysis.PDE.Schauder.nondivergenceOperator,hb]

local instance thirdDataFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance thirdDataFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance thirdDataSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdDataSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdDataEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance thirdDataEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance

/-- All flat Schauder inputs, uniformly before the nonlinear solution.
The source and coefficient fields are genuine global Hölder extensions.
Only the original C²,α, log-coefficient, and log-density-gradient bounds
enter their constants. -/
theorem exists_uniform_flat_third_equation
    (e : X ≃ₗᵢ[ℝ] E) (k : Fin m)
    {Ω K S : Set E} (hΩK : Ω ⊆ K) (hΩ : IsOpen Ω) (hS : IsOpen S)
    (hconv : Convex ℝ S) (hcompact : IsCompact (closure S))
    (hdiam : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖x-y‖ ≤ 1)
    (hinclude : closedCoordinateHalfPatch k 0 (1/2) ⊆ e ⁻¹' closure S)
    (hinterior : ∀ x ∈ ball (0 : X) (1/8), 0 < x k → e x ∈ S)
    (G P : E → E) (hG : ContDiff ℝ 4 G) (hP : ContDiff ℝ 4 P)
    (hGK : MapsTo G (closure S) K) (hGΩ : MapsTo G S Ω)
    (hinv : ∀ x ∈ closure S, (fun z => P (G z)) =ᶠ[𝓝 x] id)
    (B₀ : E → ℝ) (hB₀ : ContDiff ℝ 4 B₀)
    {α R N Z ell Λ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hR : 0 ≤ R) (hN : 0 ≤ N) (hZ : 0 ≤ Z) (hell : 0 < ell) (hΛ : 0 ≤ Λ) :
    ∃ ell' Λ' N' B V, 0 < ell' ∧ 0 ≤ Λ' ∧ 0 ≤ N' ∧ 0 < B ∧ 0 < V ∧
      ∀ p : BoundaryLogSolution e k hΩK S G B₀ α R N Z ell Λ,
        Nonempty (FlatThirdEquation k (e ⁻¹' closure S) α ell' Λ' N' B V p.flatFunction) := by
  have hz : e (0 : X) ∈ closure S := hinclude ⟨by simp,by simp⟩
  have hne : (closure S).Nonempty := ⟨e 0,hz⟩
  obtain ⟨C,M,hC,hM,hcoefficient⟩ := exists_global_elliptic_chart_matrix e G P
    (hG.of_le (by norm_num)) (hP.of_le (by norm_num)) hne hcompact hconv.closure hGK hdiam hinv
    hα.le hα1.le hell hΛ
  obtain ⟨B,hB,hsource⟩ := exists_uniform_coordinate_log_chart_sources e hΩK hΩ hS
    hconv hcompact hdiam G P hG hP hGK hGΩ (fun x hx => hinv x (subset_closure hx))
    B₀ hB₀ hα.le hα1.le hR hN hZ
  obtain ⟨V,hV,hlower⟩ := exists_chart_remainder_lower_bound e G (hG.of_le (by norm_num))
    B₀ (hB₀.of_le (by norm_num)) hcompact hconv.closure hGK (hΩK := hΩK) hα.le hα1.le hR
  refine ⟨ell/M^2,Λ*M^2,C*N,B,V,by positivity,by positivity,by positivity,hB,hV,?_⟩
  intro p
  obtain ⟨a,han,ha,hap⟩ := hcoefficient
    (fun x => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots p.u x)) p.A p.value_A
    (fun _ _ => OAI.Analysis.PDE.Dirichlet.logRealOperator_isSymmetric _) p.lower p.upper
  obtain ⟨Q,hQn,hQ⟩ := hsource p.u p.f p.U (p.smooth.of_le (by norm_num)) p.norm_U p.value_U
    p.A p.W p.norm_A p.norm_W p.value_A p.value_W p.source_differentiable p.equation
  have hflatne : (e ⁻¹' closure S).Nonempty := ⟨0,hz⟩
  have hcomplete : IsComplete (e ⁻¹' closure S) := (isClosed_closure.preimage e.continuous).isComplete
  have hflatconv : Convex ℝ (e ⁻¹' closure S) := hconv.closure.linear_preimage e.toLinearEquiv.toLinearMap
  have hext (i : Fin m) := exists_convex_holder_extension hflatne hcomplete hflatconv hα.le (Q i)
  choose F hF hFn using hext
  have hp := hap 0 hz
  have hv := hlower p.u (p.smooth.of_le (by norm_num)) p.U p.norm_U p.value_U p.first_U p.second_U
  have hψ := p.flatFunction_contDiff hG hB₀
  refine ⟨{
    coefficient := a
    source := F
    norm_coefficient := han.trans (mul_le_mul_of_nonneg_left p.norm_A hC.le)
    norm_source := fun i => (hFn i).trans (hQn i)
    positive := hp.1
    lower := hp.2.1
    upper := hp.2.2.1
    diagonal := ?_
    trace := ?_
    first := ?_
    second := ?_
    equation := ?_ }⟩
  · intro x hx hxk
    exact (hap x (hinclude ⟨(closedBall_subset_closedBall (by norm_num))
      (ball_subset_closedBall hx),hxk⟩)).2.2.2 k
  · apply coordinate_tangent_zero_of_trace k p.flatFunction (hψ.of_le (by norm_num))
    intro x hx hxk
    exact sub_eq_zero.mpr (p.trace x hx hxk)
  · intro x hx
    exact (hv x hx).1
  · intro x hx
    exact (hv x hx).2
  · intro i x hx hxk
    have hxs := hinterior x hx hxk
    rw [isometry_chart_nondivergence_eq e
      (fun z => fderiv ℝ P (G (e z)))
      (fun z => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots p.u (G (e z))))
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value a) _
      (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hψ (m := 2) (by norm_num) _)
      x (OAI.Analysis.PDE.Dirichlet.logRealOperator_isSymmetric _) (ha x (subset_closure hxs))]
    exact (hQ i x hxs).trans (hF i ⟨x,subset_closure hxs⟩).symm

end OAI.Analysis.PDE.Elliptic
