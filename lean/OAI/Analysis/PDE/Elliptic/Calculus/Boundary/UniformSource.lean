import OAI.Analysis.PDE.Elliptic.Calculus.Boundary.ActualSource
import OAI.Analysis.PDE.Elliptic.Calculus.Boundary.ChartFields

/-! Uniform forcing for the true differentiated nonlinear equation in a
fixed smooth chart. All constants precede the varying potential. -/

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion

variable {n : ℕ}
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance uniformSourceFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance uniformSourceFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance uniformSourceSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance uniformSourceSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance uniformSourceEndGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance uniformSourceEndSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance uniformSourceEndSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance uniformSourceEndSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance

private theorem source_budget_le (d p l j t b d₂ h c R N Z : ℝ)
    (hd : 0 ≤ d) (hp : 0 ≤ p) (hl : 0 ≤ l) (hj : 0 ≤ j) (ht : 0 ≤ t)
    (_ : 0 ≤ b) (hd₂ : 0 ≤ d₂) (hh : 0 ≤ h) (_ : 0 ≤ c)
    (hR : 0 ≤ R) (_ : 0 ≤ N) (_ : 0 ≤ Z)
    {u a v bb q : ℝ} (_ : 0 ≤ u) (ha : 0 ≤ a) (hv : 0 ≤ v)
    (_ : 0 ≤ bb) (huR : u ≤ R) (haN : a ≤ p*N) (hvN : v ≤ c*N)
    (hbbN : bb ≤ c*N) (hq : q ≤ 2*(p*Z)*b) :
    q+d*(8*(p*u)*a*j+4*(l*u)*a*t)+
      (8*(p*u)*b^2*v+4*(l*u)*d₂*v)+d*(2*h*bb) ≤
    2*(p*Z)*b+d*(8*(p*R)*(p*N)*j+4*(l*R)*(p*N)*t)+
      (8*(p*R)*b^2*(c*N)+4*(l*R)*d₂*(c*N))+d*(2*h*(c*N)) := by
  gcongr

theorem exists_uniform_log_chart_source
    {Ω K S : Set E} (hΩK : Ω ⊆ K) (hΩ : IsOpen Ω) (hS : IsOpen S)
    (hconv : Convex ℝ S) (hcompact : IsCompact (closure S))
    (hdiam : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖x-y‖ ≤ 1)
    (G P : E → E) (hG : ContDiff ℝ 4 G) (hP : ContDiff ℝ 4 P)
    (hGK : MapsTo G (closure S) K) (hGΩ : MapsTo G S Ω)
    (hinv : ∀ x ∈ S, (fun z => P (G z)) =ᶠ[𝓝 x] id)
    (B₀ : E → ℝ) (hB₀ : ContDiff ℝ 4 B₀) (v : E) (hv : ‖v‖ ≤ 1)
    {α R N Z : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hR : 0 ≤ R) (hN : 0 ≤ N) (hZ : 0 ≤ Z) :
    ∃ C > 0, ∀ (u f : E → ℝ) (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α),
      ContDiff ℝ 3 u → ‖U‖ ≤ R →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.value U x = u x) →
      ∀ (A : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E) α) (W : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] ℝ) α),
      ‖A‖ ≤ N → ‖W‖ ≤ Z →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value W x = (f x)⁻¹ • fderiv ℝ f x) →
      (∀ x ∈ S, DifferentiableAt ℝ f (G x)) →
      (∀ x ∈ S, (fun z => OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u z)) =ᶠ[𝓝 (G x)] f) →
      ∃ Q : OAI.Analysis.Normed.Function.Holder.HolderMap (closure S) ℝ α, ‖Q‖ ≤ C ∧
        ∀ x, ∀ hx : x ∈ S, ellipticTrace
          (fun z => pullbackEllipticOperator (fderiv ℝ P (G z))
            (OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u (G z))))
          (OAI.Analysis.PDE.Dirichlet.directionalDerivative ((fun y => u y-B₀ y) ∘ G) v) x =
            OAI.Analysis.Normed.Function.Holder.HolderMap.value Q ⟨x,subset_closure hx⟩ := by
  have hDG₃ : ContDiff ℝ 3 (fderiv ℝ G) := hG.fderiv_right (by norm_num)
  have hD₂G : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ G)) := hDG₃.fderiv_right (by norm_num)
  have hT : ContDiff ℝ 3 (chartTangentField G P v) :=
    (hDG₃.comp (hP.of_le (by norm_num))).clm_apply contDiff_const
  have hDT : ContDiff ℝ 2 (fderiv ℝ (chartTangentField G P v)) := hT.fderiv_right (by norm_num)
  have hD₂T : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (chartTangentField G P v))) := hDT.fderiv_right (by norm_num)
  obtain ⟨J,hJ⟩ := OAI.Analysis.Normed.Function.Holder.exists_fixed_holder_on_compact_convex hcompact hconv.closure hdiam _
    ((hDT.of_le (by norm_num)).comp (hG.of_le (by norm_num))) hα hα1
  obtain ⟨T,hTval⟩ := OAI.Analysis.Normed.Function.Holder.exists_fixed_holder_on_compact_convex hcompact hconv.closure hdiam _
    (hD₂T.comp (hG.of_le (by norm_num))) hα hα1
  obtain ⟨D,hD⟩ := OAI.Analysis.Normed.Function.Holder.exists_fixed_holder_on_compact_convex hcompact hconv.closure hdiam _
    (hDG₃.of_le (by norm_num)) hα hα1
  obtain ⟨D₂,hD₂⟩ := OAI.Analysis.Normed.Function.Holder.exists_fixed_holder_on_compact_convex hcompact hconv.closure hdiam _
    (hD₂G.of_le (by norm_num)) hα hα1
  have hback : ContDiff ℝ 3 (OAI.Analysis.PDE.Dirichlet.directionalDerivative (B₀ ∘ G) v) :=
    OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative (hB₀.comp hG) (by norm_num) v
  have hHback : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative (B₀ ∘ G) v))) :=
    (hback.fderiv_right (m := 2) (by norm_num)).fderiv_right (by norm_num)
  obtain ⟨H,hH⟩ := OAI.Analysis.Normed.Function.Holder.exists_fixed_holder_on_compact_convex hcompact hconv.closure hdiam _ hHback hα hα1
  obtain ⟨C₀,hC₀,hfields⟩ := exists_chart_holder_fields_on G P (hG.of_le (by norm_num))
    (hP.of_le (by norm_num)) hcompact hconv.closure hGK hdiam hα hα1
  let L := max 1 ‖D‖
  have hL : 0 ≤ L := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_left _ _)
  have hDG x (hx : x ∈ closure S) : ‖fderiv ℝ G x‖ ≤ L := by
    rw [← hD ⟨x,hx⟩]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le D _).trans (le_max_right _ _)
  let g : closure S → K := fun x => ⟨G x,hGK x.property⟩
  have hg : Continuous g := by fun_prop
  have hLip (x y : closure S) : dist (g x) (g y) ≤ L*dist x y := by
    simpa only [g, Subtype.dist_eq, dist_eq_norm] using
      hconv.closure.norm_image_sub_le_of_norm_fderiv_le
        (fun z _ => hG.differentiable (by norm_num) z) hDG y.property x.property
  let p := max 1 (L^α)
  let C := 2*(p*Z)*‖D‖ + (Module.finrank ℝ E : ℝ)*
      (8*(p*R)*(p*N)*‖J‖+4*(max 1 L*R)*(p*N)*‖T‖) +
      (8*(p*R)*‖D‖^2*(C₀*N)+4*(max 1 L*R)*‖D₂‖*(C₀*N)) +
      (Module.finrank ℝ E : ℝ)*(2*‖H‖*(C₀*N)) + 1
  have hp : 0 ≤ p := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_left _ _)
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro u f U hu hUn hU A W hAn hWn hA hW hf heq
  obtain ⟨a,ha,han⟩ := OAI.Analysis.Normed.Function.Holder.exists_holder_lipschitz_pullback hα A g hg hL hLip
  obtain ⟨w,hw,hwn⟩ := OAI.Analysis.Normed.Function.Holder.exists_holder_lipschitz_pullback hα W g hg hL hLip
  obtain ⟨b,V,hbn,hVn,hb,hV⟩ := hfields
    (fun z => OAI.Analysis.PDE.Dirichlet.logRealOperator (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u z)) A hA
  let q := OAI.Analysis.Normed.Function.Holder.HolderMap.action hα w (holderEvaluate D v)
  have hq x (hx : x ∈ S) : OAI.Analysis.Normed.Function.Holder.HolderMap.value q ⟨x,subset_closure hx⟩ =
      fderiv ℝ f (G x) (fderiv ℝ G x v) / f (G x) := by
    simp only [q, OAI.Analysis.Normed.Function.Holder.HolderMap.value_action, value_holderEvaluate, hw, hD, hW,
      smul_apply, smul_eq_mul]
    dsimp only [g]
    ring
  have hqn : ‖q‖ ≤ 2*(p*Z)*‖D‖ := by
    apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα _ _).trans
    have hw' : ‖w‖ ≤ p*Z := hwn.trans (mul_le_mul_of_nonneg_left hWn hp)
    have hd' := holderEvaluate_norm_le D hv
    gcongr
  obtain ⟨q₀,hq₀,hq₀n⟩ := exists_actual_log_chart_tangent_source U hΩ hS hconv
    (hG.of_le (by norm_num)) (hP.of_le (by norm_num)) hGK hGΩ hL hDG hα hα1 hdiam v hv
    a J D T D₂ V q u f hu hU
    (fun x hx => (ha _).trans (hA _)) hJ hTval hD hD₂
    (fun x hx => hV _) hq hf hinv heq
  refine ⟨q₀-holderEllipticTrace hα b H, ?_, ?_⟩
  · apply (norm_sub_le _ _).trans
    apply (add_le_add hq₀n (holderEllipticTrace_norm_le hα b H)).trans
    have ha' : ‖a‖ ≤ p*N := han.trans (mul_le_mul_of_nonneg_left hAn hp)
    have hb' : ‖b‖ ≤ C₀*N := hbn.trans (mul_le_mul_of_nonneg_left hAn hC₀.le)
    have hv' : ‖V‖ ≤ C₀*N := hVn.trans (mul_le_mul_of_nonneg_left hAn hC₀.le)
    exact (source_budget_le (Module.finrank ℝ E) p (max 1 L) ‖J‖ ‖T‖ ‖D‖ ‖D₂‖ ‖H‖ C₀ R N Z
      (Nat.cast_nonneg _) hp (le_trans zero_le_one (le_max_left _ _))
      (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      hC₀.le hR hN hZ (norm_nonneg U) (norm_nonneg a) (norm_nonneg V) (norm_nonneg b)
      hUn ha' hv' hb' hqn).trans (le_add_of_nonneg_right (by norm_num))
  · intro x hx
    exact chart_remainder_source hα _ G u B₀ hu (hB₀.of_le (by norm_num))
      (hG.of_le (by norm_num)) v b H q₀ hb hH ⟨x,subset_closure hx⟩ (hq₀ x hx)

end OAI.Analysis.PDE.Elliptic
