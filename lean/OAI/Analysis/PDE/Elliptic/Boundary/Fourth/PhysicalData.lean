import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.ChartAssembly
import OAI.Analysis.PDE.Elliptic.Calculus.Boundary.ChartFields
import OAI.Analysis.PDE.Elliptic.DirichletChartEllipticity

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.PDE.Dirichlet OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder OAI.Analysis.Calculus.SmoothExtension

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] in
theorem exists_fixed_chart_pullback_bound
    (G : E → E) (hG : ContDiff ℝ 1 G) {S K : Set E}
    (hS : IsCompact S) (hSc : Convex ℝ S) (hGK : MapsTo G S K)
    {α : ℝ} (hα : 0 ≤ α) :
    ∃ C > 0, ∀ U : OAI.Analysis.Normed.Function.Holder.HolderMap K F α, ∃ V : OAI.Analysis.Normed.Function.Holder.HolderMap S F α,
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = OAI.Analysis.Normed.Function.Holder.HolderMap.value U ⟨G x,hGK x.property⟩) ∧
      ‖V‖ ≤ C*‖U‖ := by
  obtain ⟨R,hR⟩ := hS.exists_bound_of_continuousOn (hG.continuous_fderiv one_ne_zero).continuousOn
  let L := max 1 R
  have hL : 0 ≤ L := le_trans zero_le_one (le_max_left _ _)
  let g : S → K := fun x => ⟨G x,hGK x.property⟩
  have hg : Continuous g := (hG.continuous.comp continuous_subtype_val).subtype_mk _
  have hLip (x y : S) : dist (g x) (g y) ≤ L*dist x y := by
    have he := hSc.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hG.differentiable one_ne_zero z)
      (fun z hz => (hR z hz).trans (le_max_right 1 R)) y.property x.property
    simpa only [g,Subtype.dist_eq,dist_eq_norm] using he
  refine ⟨max 1 (L^α),lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro U
  exact OAI.Analysis.Normed.Function.Holder.exists_holder_lipschitz_pullback hα U g hg hL hLip

variable {m : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin m)
local instance physicalFourth1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance physicalFourth1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance physicalFourth2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance physicalFourth2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance physicalFourth3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance physicalFourth3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

/-- The boundary fourth-order estimate with only physical coefficient and
source data as inputs. Coordinate ellipticity, coefficient transport and
all chart drift terms are constructed internally and uniformly. -/
theorem exists_fourth_chart_bound_of_physical_data
    (e : X ≃ₗᵢ[ℝ] E) {G P : E → E} (hG : ContDiff ℝ 4 G) (hP : ContDiff ℝ 3 P)
    {S Ω K : Set E} (hS : IsCompact S) (hSc : Convex ℝ S)
    (hGK : MapsTo G S K) {hΩK : Ω ⊆ K}
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ 1)
    (hinv : ∀ z ∈ S, (fun y => P (G y)) =ᶠ[𝓝 z] id)
    {α ell Λ N : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hell : 0 < ell) (hΛ : 0 ≤ Λ) (hN : 0 ≤ N) :
    ∃ C > 0, ∀ (u : E → ℝ), ContDiff ℝ 4 u →
      ∀ (T : Fin m → E → E), (∀ i, ContDiff ℝ 3 (T i)) → ∀ k : Fin m,
      (∀ i z, z ∈ S → T i =ᶠ[𝓝 (G z)] chartTangentField G P (e (EuclideanSpace.single i 1))) →
      ∀ (A : E → E →L[ℝ] E) (a : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E) α),
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value a x = A x) → ‖a‖ ≤ N →
      (∀ x ∈ K, (A x).toLinearMap.IsSymmetric) →
      (∀ x ∈ K, ∀ v, ell*‖v‖^2 ≤ inner ℝ v (A x v)) →
      (∀ x ∈ K, ∀ v, inner ℝ v (A x v) ≤ Λ*‖v‖^2) →
      ∀ D : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ (fderiv ℝ (fderiv ℝ (u ∘ G))) x) →
      ∀ M Q L : ℝ, 0 ≤ M → 0 ≤ Q → 0 ≤ L → ‖D‖ ≤ L →
      (∀ i, i ≠ k → ∀ j, j ≠ k → ∃ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α,
        ‖U‖ ≤ M ∧
        (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = fieldDerivative (fieldDerivative u (T i)) (T j) x) ∧
        (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x =
          fderiv ℝ (fieldDerivative (fieldDerivative u (T i)) (T j)) x) ∧
        (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x =
          fderiv ℝ (fderiv ℝ (fieldDerivative (fieldDerivative u (T i)) (T j))) x)) →
      ∀ R : Fin m → OAI.Analysis.Normed.Function.Holder.HolderMap K ℝ α, (∀ i, ‖R i‖ ≤ Q) →
      (∀ i (x : K), OAI.Analysis.Normed.Function.Holder.HolderMap.value (R i) x =
        ellipticTrace A (fieldDerivative (fieldDerivative u (T i)) (T k)) x) →
      HasFourthHolderBound S α (u ∘ G) (C*(M+Q+L)) := by
  obtain ⟨Cc,hCc,hcoeff⟩ := exists_chart_holder_fields_on G P
    (hG.of_le (by norm_num)) (hP.of_le (by norm_num)) hS hSc hGK hdiam hα hα1
  obtain ⟨Cp,hCp,hpull⟩ := exists_fixed_chart_pullback_bound (F := ℝ) G
    (hG.of_le (by norm_num)) hS hSc hGK hα
  obtain ⟨J₀,hJ₀⟩ := hS.exists_bound_of_continuousOn
    ((hP.continuous_fderiv (by norm_num)).comp hG.continuous).continuousOn
  obtain ⟨D₀,hD₀⟩ := hS.exists_bound_of_continuousOn (hG.continuous_fderiv (by norm_num)).continuousOn
  let B := max 1 (max J₀ D₀)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hJ z (hz : z ∈ S) : ‖fderiv ℝ P (G z)‖ ≤ B :=
    (hJ₀ z hz).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hDG z (hz : z ∈ S) : ‖fderiv ℝ G z‖ ≤ B :=
    (hD₀ z hz).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hμ : 0 < ell/B^2 := div_pos hell (sq_pos_of_pos hB)
  obtain ⟨Cr,hCr,hchart⟩ := exists_fourth_chart_bound e hG hP hS hSc hGK
    (hΩK := hΩK) hα hα1 hμ (mul_nonneg hCc.le hN)
  refine ⟨Cr*(1+Cp+2*Cc*N),mul_pos hCr (by positivity),?_⟩
  intro u hu T hT k hTg A a ha han hsym hlo hhi D hD M Q L hM hQ hL hDn hjets R hRn hR
  obtain ⟨Ac,V,hAcn,hVn,hAc,hV⟩ := hcoeff A a ha
  have hnormal (x : S) : ell/B^2 ≤ inner ℝ
      (pullbackEllipticOperator (fderiv ℝ P (G x)) (A (G x))
        (e (EuclideanSpace.single k 1))) (e (EuclideanSpace.single k 1)) := by
    have hi : (fderiv ℝ P (G x)).comp (fderiv ℝ G x) = ContinuousLinearMap.id ℝ E :=
      clm_left_inverse_comm _ _ (inverse_jacobian_of_local_right_inverse
        (hP.differentiable (by norm_num) _) (hG.differentiable (by norm_num) _)
        (hinv x x.property))
    have he := (pullbackEllipticOperator_uniform_bounds _ _ _ hi hB
      (hJ x x.property) (hDG x x.property) hell.le hΛ
      (hlo (G x) (hGK x.property)) (hhi (G x) (hGK x.property))
      (e (EuclideanSpace.single k 1))).1
    rw [real_inner_comm]
    simpa only [e.norm_map,PiLp.norm_single,norm_one,one_pow,mul_one] using he
  have hRex (i : Fin m) := hpull (R i)
  choose R' hR' hR'n using hRex
  have hb := hchart u hu T hT k hinv hTg A Ac hAc
    (hAcn.trans (mul_le_mul_of_nonneg_left han hCc.le)) hsym hnormal
    D V hD hV M (Cp*Q) hM (mul_nonneg hCp.le hQ) hjets R'
    (fun i => (hR'n i).trans (mul_le_mul_of_nonneg_left (hRn i) hCp.le))
    (fun i x => (hR' i x).trans (hR i ⟨G x,hGK x.property⟩))
  have hVbound : ‖V‖ ≤ Cc*N := hVn.trans (mul_le_mul_of_nonneg_left han hCc.le)
  have hCN : 0 ≤ 2*Cc*N := by positivity
  apply hb.mono
  calc
    Cr*(M+Cp*Q+2*‖D‖*‖V‖) ≤ Cr*(M+Cp*Q+(2*Cc*N)*L) := by
      apply mul_le_mul_of_nonneg_left _ hCr.le
      have ht := mul_le_mul (mul_le_mul_of_nonneg_left hDn (by norm_num : (0:ℝ) ≤ 2))
        hVbound (norm_nonneg V) (by positivity : 0 ≤ 2*L)
      nlinarith
    _ ≤ Cr*((1+Cp+2*Cc*N)*(M+Q+L)) := by
      apply mul_le_mul_of_nonneg_left _ hCr.le
      nlinarith [mul_nonneg hCp.le hM,mul_nonneg hCN hM,
        mul_nonneg hCN hQ,mul_nonneg hCp.le hL]
    _ = Cr*(1+Cp+2*Cc*N)*(M+Q+L) := by ring

end OAI.Analysis.PDE.Elliptic
