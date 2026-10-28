import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.IsometryRecovery
import OAI.Analysis.PDE.Elliptic.Boundary.DoubleTangentChart

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.Calculus.SmoothExtension

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {m : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin m)
local instance fourthAssembly1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthAssembly1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthAssembly2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthAssembly2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthAssembly3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthAssembly3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem pullback_operator_isSymmetric (J A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) :
    (pullbackEllipticOperator J A).toLinearMap.IsSymmetric := by
  intro x y
  change inner ℝ (J (A (J.adjoint x))) y = inner ℝ x (J (A (J.adjoint y)))
  rw [← J.adjoint_inner_right, ← J.adjoint_inner_left]
  exact hA _ _

/-- Full fourth-order chart control from the genuine twice-tangential
Dirichlet estimates and the genuine normal differentiated equations.
Only the third jet occurs in the chart drift. All constants precede u. -/
theorem exists_fourth_chart_bound
    (e : X ≃ₗᵢ[ℝ] E) {G P : E → E} (hG : ContDiff ℝ 4 G) (hP : ContDiff ℝ 3 P)
    {S Ω K : Set E} (hS : IsCompact S) (hSc : Convex ℝ S)
    (hGK : MapsTo G S K) {hΩK : Ω ⊆ K} {α μ N : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) (hμ : 0 < μ) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (u : E → ℝ), ContDiff ℝ 4 u →
      ∀ (T : Fin m → E → E), (∀ i, ContDiff ℝ 3 (T i)) → ∀ k : Fin m,
      (∀ z ∈ S, (fun y => P (G y)) =ᶠ[𝓝 z] id) →
      (∀ i z, z ∈ S → T i =ᶠ[𝓝 (G z)] chartTangentField G P (e (EuclideanSpace.single i 1))) →
      ∀ (A : E → E →L[ℝ] E) (Ac : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E) α),
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value Ac x =
        pullbackEllipticOperator (fderiv ℝ P (G x)) (A (G x))) → ‖Ac‖ ≤ N →
      (∀ x ∈ K, (A x).toLinearMap.IsSymmetric) →
      (∀ x : S, μ ≤ inner ℝ
        (pullbackEllipticOperator (fderiv ℝ P (G x)) (A (G x))
          (e (EuclideanSpace.single k 1))) (e (EuclideanSpace.single k 1))) →
      ∀ (D : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α) (V : OAI.Analysis.Normed.Function.Holder.HolderMap S E α),
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ G))) x) →
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = inverseChartDrift A G P x) →
      ∀ M Q : ℝ, 0 ≤ M → 0 ≤ Q →
      (∀ i, i ≠ k → ∀ j, j ≠ k → ∃ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α,
        ‖U‖ ≤ M ∧
        (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = fieldDerivative (fieldDerivative u (T i)) (T j) x) ∧
        (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x =
          fderiv ℝ (fieldDerivative (fieldDerivative u (T i)) (T j)) x) ∧
        (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x =
          fderiv ℝ (fderiv ℝ (fieldDerivative (fieldDerivative u (T i)) (T j))) x)) →
      ∀ F : Fin m → OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α,
      (∀ i, ‖F i‖ ≤ Q) →
      (∀ i (x : S), OAI.Analysis.Normed.Function.Holder.HolderMap.value (F i) x =
        ellipticTrace A (fieldDerivative (fieldDerivative u (T i)) (T k)) (G x)) →
      HasFourthHolderBound S α (u ∘ G) (C*(M+Q+2*‖D‖*‖V‖)) := by
  classical
  obtain ⟨Ct,hCt,hchart⟩ := exists_double_tangent_chart_holder
    (hG.of_le (by norm_num)) hP hS hSc hGK (hΩK := hΩK) hα hα1
  obtain ⟨Cr,hCr,hrecover⟩ := exists_uniform_fourth_holder_in_frame e hα hμ hN
  refine ⟨Cr*(Ct+1),mul_pos hCr (by linarith),?_⟩
  intro u hu T hT k hinv hTg A Ac hAc hAcn hsym hpos D V hD hV M Q hM hQ hjets F hFn hF
  have hv (i : Fin m) : ‖e (EuclideanSpace.single i 1)‖ ≤ 1 := by simp
  have hRex (i : Fin m) := exists_double_field_chart_source A hG hP hu
    (hT i) ((hT k).of_le (by norm_num)) hα
    (e (EuclideanSpace.single i 1)) (e (EuclideanSpace.single k 1)) (hv i) (hv k)
    hinv (hTg i) (hTg k) (F i) D V (hF i) hD hV
  choose R hR hRn using hRex
  have hBex (p : Fin m × Fin m) :
      ∃ H : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] ℝ) α, ‖H‖ ≤ Ct*M ∧
        (p.1 ≠ k → p.2 ≠ k → ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x =
          fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative
            (OAI.Analysis.PDE.Dirichlet.directionalDerivative (u ∘ G) (e (EuclideanSpace.single p.1 1)))
            (e (EuclideanSpace.single p.2 1)))) x) := by
    by_cases hi : p.1 = k
    · exact ⟨0,by simpa only [norm_zero] using mul_nonneg hCt.le hM,fun hn => (hn hi).elim⟩
    by_cases hj : p.2 = k
    · exact ⟨0,by simpa only [norm_zero] using mul_nonneg hCt.le hM,fun _ hn => (hn hj).elim⟩
    obtain ⟨U,hUn,hU₀,hU₁,hU₂⟩ := hjets p.1 hi p.2 hj
    obtain ⟨H,hH,hHn⟩ := hchart u (T p.1) (T p.2) hu (hT p.1)
      ((hT p.2).of_le (by norm_num))
      (e (EuclideanSpace.single p.1 1)) (e (EuclideanSpace.single p.2 1))
      hinv (hTg p.1) (hTg p.2) U hU₀ hU₁ hU₂
    exact ⟨H,hHn.trans (mul_le_mul_of_nonneg_left hUn hCt.le),fun _ _ => hH⟩
  choose B hBn hB using hBex
  have hQ' : 0 ≤ Q+2*‖D‖*‖V‖ := by positivity
  have hbound := hrecover S (u ∘ G) (hu.comp hG) k
    (fun y => pullbackEllipticOperator (fderiv ℝ P (G y)) (A (G y)))
    Ac R B hAc hAcn
    (fun x => pullback_operator_isSymmetric _ _ (hsym (G x) (hGK x.property)))
    (fun i hi j hj => hB (i,j) hi hj) (Ct*M) (Q+2*‖D‖*‖V‖)
    (mul_nonneg hCt.le hM) hQ' (fun i _ j _ => hBn (i,j))
    (fun i => (hRn i).trans (add_le_add (hFn i) le_rfl)) hpos hR
  apply hbound.mono
  calc
    Cr*(Ct*M+(Q+2*‖D‖*‖V‖)) ≤ Cr*((Ct+1)*(M+Q+2*‖D‖*‖V‖)) := by
      apply mul_le_mul_of_nonneg_left _ hCr.le
      nlinarith [mul_nonneg hCt.le hQ']
    _ = Cr*(Ct+1)*(M+Q+2*‖D‖*‖V‖) := by ring

end OAI.Analysis.PDE.Elliptic
