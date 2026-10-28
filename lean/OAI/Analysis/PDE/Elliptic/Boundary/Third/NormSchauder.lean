import OAI.Analysis.PDE.Elliptic.Boundary.Third.LocalSchauder
import OAI.Analysis.PDE.Schauder.Calculus.Interior.ThirdJet
import OAI.Analysis.PDE.Dirichlet.Periodic.Chart.LocalizationUniform

/-! The boundary third-order estimate with the actual global third-jet norm
as its small error. The artificial cutoff seminorm has been eliminated. -/

noncomputable section
open Set Metric InnerProductSpace
open scoped Matrix.Norms.Elementwise
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.PDE.Dirichlet

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

local instance thirdNormFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance thirdNormFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance thirdNormSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdNormSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdNormThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance thirdNormThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem exists_third_directional_cutoff (k : Fin m)
    {Ω K : Set E} (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K)
    (hinclude : closedCoordinateHalfPatch k 0 (1/2) ⊆ K)
    {α r M : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hr : 0 < r) (hM : 0 ≤ M)
    (hrM : r*M < (1/2 : ℝ)/2) :
    ∃ CH > 0, ∀ L : E ≃L[ℝ] E, ‖L.toContinuousLinearMap‖ ≤ M →
      (∃ c > 0, ∀ z : E, L z k = c*z k) →
      ∀ u : E → ℝ, ContDiff ℝ 3 u → ∀ V, 0 ≤ V →
      ∀ T : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) →
      (∀ x ∈ K, ‖fderiv ℝ u x‖ ≤ V) →
      (∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ V) →
      ∀ i : Fin m, ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ (fun z => OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z *
            OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1) (L (r • z)))) x -
          fderiv ℝ (fderiv ℝ (fun z => OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z *
            OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1) (L (r • z)))) y‖ ≤
              (CH*(V+‖T‖))*‖x-y‖^α := by
  have himage : MapsTo (id : E → E) ({x | 0 ≤ x k} ∩ closedBall 0 (1/2)) K := by
    intro x hx
    exact hinclude ⟨hx.2, hx.1⟩
  obtain ⟨CH, hCH, hcutoff⟩ := OAI.Analysis.PDE.Dirichlet.exists_uniform_halfspace_equiv_chart_hessian_bound
    k (id : E → E) contDiff_id (by norm_num : (0 : ℝ) < 1/2) hr hM
      hrM himage (hΩK := hΩK) hα hα1
  refine ⟨CH, hCH, ?_⟩
  intro L hL hLplane u hu V hV T hT hDu hD₂u i
  obtain ⟨U, hUn, hU0, hU1, hU2⟩ := OAI.Analysis.PDE.Schauder.exists_directional_C2Holder hΩ hΩK hα hV
    u hu T hT hDu hD₂u (EuclideanSpace.single i 1) (by simp)
  have hw : ContDiff ℝ 2 (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1)) :=
    OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (m := 2) (by norm_num) _
  have hh := (hcutoff L hL hLplane _ hw U hU0 hU1 hU2).2
  intro x hx y hy
  apply (show _ ≤ CH*‖U‖*‖x-y‖^α by simpa only [id_eq] using hh x hx y hy).trans
  gcongr

theorem boundary_third_norm_schauder (hm : 3 ≤ m) (k : Fin m)
    {Ω K : Set E} (hΩ : IsOpen Ω) (hΩK : Ω ⊆ K)
    (hinclude : closedCoordinateHalfPatch k 0 (1/2) ⊆ K)
    {α ell Λ N μ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hell : 0 < ell) (hΛ : 0 ≤ Λ) (hN : 0 ≤ N) (hμ : 0 < μ) :
    ∃ δ > 0, ∀ ε > 0, ∃ D > 0,
      ∀ A : OAI.Analysis.Normed.Function.Holder.HolderMap E (Matrix (Fin m) (Fin m) ℝ) α, ‖A‖ ≤ N →
      (OAI.Analysis.Normed.Function.Holder.HolderMap.value A 0).PosDef →
      (∀ v : E, ell*‖v‖^2 ≤ inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (OAI.Analysis.Normed.Function.Holder.HolderMap.value A 0) v)) →
      (∀ v : E, inner ℝ v (Matrix.toEuclideanCLM (𝕜 := ℝ) (OAI.Analysis.Normed.Function.Holder.HolderMap.value A 0) v) ≤ Λ*‖v‖^2) →
      (∀ x ∈ ball 0 (1/8), 0 ≤ x k → μ ≤ OAI.Analysis.Normed.Function.Holder.HolderMap.value A x k k) →
      ∀ u : E → ℝ, ContDiff ℝ 4 u →
      (∀ i, i ≠ k → ∀ x ∈ ball 0 (1/8), x k = 0 →
        OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1) x = 0) →
      ∀ F : Fin m → OAI.Analysis.Normed.Function.Holder.HolderMap E ℝ α, ∀ B V, 0 ≤ B → 0 ≤ V →
      (∀ i, ‖F i‖ ≤ B) →
      (∀ x ∈ K, ‖fderiv ℝ u x‖ ≤ V) →
      (∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ V) →
      (∀ i, ∀ x ∈ ball 0 (1/8), 0 < x k →
        OAI.Analysis.PDE.Schauder.nondivergenceOperator (OAI.Analysis.Normed.Function.Holder.HolderMap.value A)
          (OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1)) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value (F i) x) →
      ∀ T : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) →
      (∀ x ∈ ball 0 δ, 0 ≤ x k →
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ ε*‖T‖+D*(B+V)) ∧
      ∀ x ∈ ball 0 δ, 0 ≤ x k → ∀ y ∈ ball 0 δ, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
          (ε*‖T‖+D*(B+V))*‖x-y‖^α := by
  obtain ⟨r, hr, hrone, hrnear, δ, hδ, hlocal⟩ :=
    uniform_boundary_third_schauder hm k hα hα1 hell hΛ hN hμ (by norm_num : (0 : ℝ) < 1/8)
  have hrK : r*Real.sqrt Λ < (1/2 : ℝ)/2 := by
    have hlt := (lt_div_iff₀ (by positivity : 0 < Real.sqrt Λ+1)).mp hrnear
    nlinarith
  obtain ⟨CH, hCH, hcutoff⟩ := exists_third_directional_cutoff k hΩ hΩK hinclude
    hα.le hα1.le hr (Real.sqrt_nonneg Λ) hrK
  refine ⟨δ, hδ, ?_⟩
  intro ε hε
  obtain ⟨D₀, hD₀, hlocal⟩ := hlocal (ε/(CH+1)) (div_pos hε (by positivity))
  refine ⟨D₀+ε+1, by positivity, ?_⟩
  intro A hAn hA hlo hhi hdiag u hu hz F B V hB hV hFn hDu hD₂u he T hT
  obtain ⟨L, hLplane, hL, hLi, hestimate⟩ :=
    hlocal A hAn 0 (by simp) hA hlo hhi hdiag
  have hsmallK (x : E) (hx : x ∈ ball 0 (1/8)) (hxk : 0 ≤ x k) : x ∈ K :=
    hinclude ⟨(closedBall_subset_closedBall (by norm_num)) (ball_subset_closedBall hx), hxk⟩
  have hcut (i : Fin m) : ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
      ‖fderiv ℝ (fderiv ℝ (fun z => OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z *
          OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1) (0+L (r • z)))) x -
        fderiv ℝ (fderiv ℝ (fun z => OAI.Analysis.PDE.Schauder.radialCutoff (1/2) z *
          OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1) (0+L (r • z)))) y‖ ≤
            (CH*(V+‖T‖))*‖x-y‖^α := by
    simpa only [zero_add] using
      hcutoff L hL hLplane u (hu.of_le (by norm_num)) V hV T hT hDu hD₂u i
  have hbound (i) (hi : i ≠ k) (x : E) (hx : x ∈ ball 0 (1/8)) (hxk : 0 ≤ x k) :
      |OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1) x| ≤ V := by
    have hh := (fderiv ℝ u x).le_opNorm (EuclideanSpace.single i 1)
    have hh' : |OAI.Analysis.PDE.Dirichlet.directionalDerivative u (EuclideanSpace.single i 1) x| ≤ ‖fderiv ℝ u x‖ := by
      simpa only [OAI.Analysis.PDE.Dirichlet.directionalDerivative, Real.norm_eq_abs,
        PiLp.norm_single, abs_one, mul_one] using hh
    exact hh'.trans (hDu x (hsmallK x hx hxk))
  obtain ⟨hpoint, hholder⟩ := hestimate u hu hz F (CH*(V+‖T‖)) V B
    (by positivity) hV hB hFn hbound he (fun i _ => hcut i)
  have hbudget : ε/(CH+1)*(CH*(V+‖T‖))+D₀*(B+V) ≤ ε*‖T‖+(D₀+ε+1)*(B+V) := by
    have hc : CH/(CH+1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
    have hs : ε/(CH+1)*(CH*(V+‖T‖)) ≤ ε*(V+‖T‖) := by
      calc
        _ = (CH/(CH+1))*(ε*(V+‖T‖)) := by ring
        _ ≤ 1*(ε*(V+‖T‖)) := mul_le_mul_of_nonneg_right hc (by positivity)
        _ = _ := one_mul _
    nlinarith
  constructor
  · intro x hx hxk
    exact (hpoint x hx hxk).trans hbudget
  · intro x hx hxk y hy hyk
    exact (hholder x hx hxk y hy hyk).trans
      (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg (norm_nonneg _) α))

end OAI.Analysis.PDE.Elliptic
