import OAI.Analysis.PDE.Elliptic.Calculus.Boundary.GlobalMatrix
import OAI.Analysis.PDE.Dirichlet.Boundary.ChartData

noncomputable section
open Set Filter InnerProductSpace
open scoped Topology Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {m : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin m)

theorem chart_conjugate_ellipticity (e : X ≃ₗᵢ[ℝ] E) (J D A : E →L[ℝ] E)
    (hinv : J.comp D = ContinuousLinearMap.id ℝ E)
    (hA : A.toLinearMap.IsSymmetric) {M ell Λ : ℝ}
    (hM : 0 < M) (hJ : ‖J‖ ≤ M) (hD : ‖D‖ ≤ M) (hell : 0 < ell) (hΛ : 0 ≤ Λ)
    (hlo : ∀ v, ell*‖v‖^2 ≤ inner ℝ v (A v))
    (hhi : ∀ v, inner ℝ v (A v) ≤ Λ*‖v‖^2) :
    let B := OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix (OAI.Analysis.PDE.Dirichlet.isometryConjugate e (pullbackEllipticOperator J A))
    B.PosDef ∧
      (∀ v : X, (ell/M^2)*‖v‖^2 ≤ inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) B v)) ∧
      (∀ v : X, inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) B v) ≤ (Λ*M^2)*‖v‖^2) ∧
      (∀ k : Fin m, ell/M^2 ≤ B k k) := by
  dsimp only
  rw [OAI.Analysis.PDE.Dirichlet.isometryConjugate_pullback]
  have hi : (OAI.Analysis.PDE.Dirichlet.isometryConjugate e J).comp (OAI.Analysis.PDE.Dirichlet.isometryConjugate e D) = ContinuousLinearMap.id ℝ X := by
    rw [OAI.Analysis.PDE.Dirichlet.isometryConjugate_comp,hinv]
    ext v
    simp only [OAI.Analysis.PDE.Dirichlet.isometryConjugate_apply,ContinuousLinearMap.id_apply,e.symm_apply_apply]
  have hl (v : X) : ell*‖v‖^2 ≤ inner ℝ v (OAI.Analysis.PDE.Dirichlet.isometryConjugate e A v) := by
    rw [real_inner_comm,OAI.Analysis.PDE.Dirichlet.inner_isometryConjugate,real_inner_comm]
    simpa only [e.norm_map] using hlo (e v)
  have hh (v : X) : inner ℝ v (OAI.Analysis.PDE.Dirichlet.isometryConjugate e A v) ≤ Λ*‖v‖^2 := by
    rw [real_inner_comm,OAI.Analysis.PDE.Dirichlet.inner_isometryConjugate,real_inner_comm]
    simpa only [e.norm_map] using hhi (e v)
  obtain ⟨hp,hlo',hhi'⟩ := OAI.Analysis.PDE.Dirichlet.chart_matrix_ellipticity (OAI.Analysis.PDE.Dirichlet.isometryConjugate e J)
    (OAI.Analysis.PDE.Dirichlet.isometryConjugate e D) (OAI.Analysis.PDE.Dirichlet.isometryConjugate e A) hi (OAI.Analysis.PDE.Dirichlet.isometryConjugate_isSymmetric e A hA)
    hM (by simpa only [OAI.Analysis.PDE.Dirichlet.norm_isometryConjugate] using hJ)
    (by simpa only [OAI.Analysis.PDE.Dirichlet.norm_isometryConjugate] using hD) hell hΛ hl hh
  refine ⟨hp,hlo',hhi',?_⟩
  intro k
  have hs := OAI.Analysis.PDE.Schauder.pullback_coefficient_isSymmetric (OAI.Analysis.PDE.Dirichlet.isometryConjugate e J) (OAI.Analysis.PDE.Dirichlet.isometryConjugate e A)
    (OAI.Analysis.PDE.Dirichlet.isometryConjugate_isSymmetric e A hA)
  have h := hlo' (EuclideanSpace.single k 1)
  rw [OAI.Analysis.PDE.Schauder.toEuclideanCLM_euclideanCoefficientMatrix _ hs] at h
  change ell/M^2 ≤ inner ℝ
    (pullbackEllipticOperator (OAI.Analysis.PDE.Dirichlet.isometryConjugate e J) (OAI.Analysis.PDE.Dirichlet.isometryConjugate e A)
      (EuclideanSpace.single k 1)) (EuclideanSpace.single k 1)
  rw [real_inner_comm]
  simpa only [PiLp.norm_single,norm_one,one_pow,mul_one] using h

/-- One global matrix field and quantitative ellipticity on the entire
closed patch, with all constants chosen before the varying coefficient. -/
theorem exists_global_elliptic_chart_matrix
    (e : X ≃ₗᵢ[ℝ] E) (G P : E → E) (hG : ContDiff ℝ 3 G) (hP : ContDiff ℝ 2 P)
    {S K : Set E} (hne : S.Nonempty) (hS : IsCompact S) (hconv : Convex ℝ S)
    (hGK : MapsTo G S K) (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ 1)
    (hinv : ∀ x ∈ S, (fun z => P (G z)) =ᶠ[𝓝 x] id)
    {α ell Λ : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hell : 0 < ell) (hΛ : 0 ≤ Λ) :
    ∃ C M, 0 < C ∧ 0 < M ∧ ∀ (A : E → E →L[ℝ] E) (a : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E) α),
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value a x = A x) →
      (∀ x ∈ K, (A x).toLinearMap.IsSymmetric) →
      (∀ x ∈ K, ∀ v, ell*‖v‖^2 ≤ inner ℝ v (A x v)) →
      (∀ x ∈ K, ∀ v, inner ℝ v (A x v) ≤ Λ*‖v‖^2) →
      ∃ B : OAI.Analysis.Normed.Function.Holder.HolderMap X (Matrix (Fin m) (Fin m) ℝ) α,
        ‖B‖ ≤ C*‖a‖ ∧
        (∀ x, e x ∈ S → OAI.Analysis.Normed.Function.Holder.HolderMap.value B x = OAI.Analysis.PDE.Schauder.euclideanCoefficientMatrix
          (OAI.Analysis.PDE.Dirichlet.isometryConjugate e (pullbackEllipticOperator (fderiv ℝ P (G (e x))) (A (G (e x)))))) ∧
        ∀ x, e x ∈ S → (OAI.Analysis.Normed.Function.Holder.HolderMap.value B x).PosDef ∧
          (∀ v : X, (ell/M^2)*‖v‖^2 ≤ inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (OAI.Analysis.Normed.Function.Holder.HolderMap.value B x) v)) ∧
          (∀ v : X, inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (OAI.Analysis.Normed.Function.Holder.HolderMap.value B x) v) ≤ (Λ*M^2)*‖v‖^2) ∧
          (∀ k : Fin m, ell/M^2 ≤ OAI.Analysis.Normed.Function.Holder.HolderMap.value B x k k) := by
  obtain ⟨C,hC,hfield⟩ := exists_global_chart_matrix e G P hG hP hne hS hconv hGK hdiam hα hα1
  obtain ⟨M₀,hM₀⟩ := hS.exists_bound_of_continuousOn
    (hG.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨M₁,hM₁⟩ := hS.exists_bound_of_continuousOn
    (((hP.continuous_fderiv (by norm_num)).comp hG.continuous).continuousOn)
  let M := max 1 (max M₀ M₁)
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hD x (hx : x ∈ S) : ‖fderiv ℝ G x‖ ≤ M :=
    (hM₀ x hx).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hJ x (hx : x ∈ S) : ‖fderiv ℝ P (G x)‖ ≤ M :=
    (hM₁ x hx).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨C,M,hC,hM,?_⟩
  intro A a ha hs hl hh
  obtain ⟨B,hBn,hB⟩ := hfield A a ha
  refine ⟨B,hBn,hB,?_⟩
  intro x hx
  rw [hB x hx]
  have hi : (fderiv ℝ P (G (e x))).comp (fderiv ℝ G (e x)) = ContinuousLinearMap.id ℝ E :=
    clm_left_inverse_comm _ _ (inverse_jacobian_of_local_right_inverse
      (hP.differentiable (by norm_num) _) (hG.differentiable (by norm_num) _) (hinv (e x) hx))
  exact chart_conjugate_ellipticity e _ _ _ hi (hs _ (hGK hx)) hM (hJ _ hx) (hD _ hx)
    hell hΛ (hl _ (hGK hx)) (hh _ (hGK hx))

end OAI.Analysis.PDE.Elliptic
