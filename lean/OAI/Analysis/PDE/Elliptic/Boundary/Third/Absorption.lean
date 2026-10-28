import OAI.Analysis.PDE.Elliptic.Boundary.SubtractedChartHolder
import OAI.Analysis.PDE.Elliptic.Boundary.Third.Coverage
import OAI.Analysis.PDE.Elliptic.Calculus.Boundary.ThirdReturn
import OAI.Analysis.PDE.Elliptic.Calculus.Boundary.RemainderJets

/-! Returning the nonlinear boundary estimate to physical coordinates.
The physical radius is fixed before the absorption parameter, and every
constant is fixed before the solution. -/

noncomputable section
open Set Filter Metric
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Schauder

local instance boundGenericFirstGroup (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedAddCommGroup (F →L[ℝ] ℝ) := inferInstance
local instance boundGenericFirstSpace (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedSpace ℝ (F →L[ℝ] ℝ) := inferInstance
local instance boundGenericSecondGroup (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance
local instance boundGenericSecondSpace (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance
local instance boundGenericThirdGroup (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedAddCommGroup (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) := inferInstance
local instance boundGenericThirdSpace (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    NormedSpace ℝ (F →L[ℝ] F →L[ℝ] F →L[ℝ] ℝ) := inferInstance

def ThirdDerivativeBound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (u : F → ℝ) (S : Set F) (α M : ℝ) : Prop :=
  (∀ x ∈ S, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ M) ∧
  (∀ x ∈ S, ∀ y ∈ S, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x-
    fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤ M*‖x-y‖^α)

theorem ThirdDerivativeBound.mono {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : F → ℝ} {S : Set F} {α M N : ℝ} (h : ThirdDerivativeBound u S α M)
    (hMN : M ≤ N) : ThirdDerivativeBound u S α N :=
  ⟨fun x hx => (h.1 x hx).trans hMN, fun x hx y hy => (h.2 x hx y hy).trans
    (mul_le_mul_of_nonneg_right hMN (by positivity))⟩

theorem third_return_small_error {C A ε R V D T Y : ℝ}
    (hC : 0 < C) (hA : 0 < A) (hε : 0 < ε) (hY : Y ≤ A*(1+R+T)) :
    C*(1+V+(ε/(C*A)*Y+D)) ≤ ε*T+C*(1+V+ε/(C*A)*A*(1+R)+D) := by
  have hμ : 0 ≤ ε/(C*A) := by positivity
  calc
    _ ≤ C*(1+V+(ε/(C*A)*(A*(1+R+T))+D)) := by gcongr
    _ = (C*(ε/(C*A))*A)*T+C*(1+V+ε/(C*A)*A*(1+R)+D) := by ring
    _ = _ := by congr 2; field_simp

variable {m n : ℕ}
local notation "X" => EuclideanSpace ℝ (Fin m)
local notation "E" => OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4
local instance physicalThirdFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance physicalThirdFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance physicalThirdSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance physicalThirdSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance physicalThirdThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance physicalThirdThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance physicalThirdFlatFirstGroup : NormedAddCommGroup (X →L[ℝ] ℝ) := inferInstance
local instance physicalThirdFlatFirstSpace : NormedSpace ℝ (X →L[ℝ] ℝ) := inferInstance
local instance physicalThirdFlatSecondGroup : NormedAddCommGroup (X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance physicalThirdFlatSecondSpace : NormedSpace ℝ (X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance physicalThirdFlatThirdGroup : NormedAddCommGroup (X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance physicalThirdFlatThirdSpace : NormedSpace ℝ (X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) := inferInstance

theorem exists_uniform_subtracted_flat_holder
    (e : X ≃ₗᵢ[ℝ] E) {Ω K S : Set E} (hΩK : Ω ⊆ K)
    (hS : IsOpen S) (hconv : Convex ℝ S) (hcompact : IsCompact (closure S))
    (hdiam : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖x-y‖ ≤ 1)
    (G : E → E) (hG : ContDiff ℝ 4 G) (hGK : MapsTo G (closure S) K)
    (hGΩ : MapsTo G S Ω) (B₀ : E → ℝ) (hB₀ : ContDiff ℝ 4 B₀)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ A > 0, ∀ u : E → ℝ, ContDiff ℝ 4 u →
      ∀ U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α,
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U x = fderiv ℝ u x) →
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U x = fderiv ℝ (fderiv ℝ u) x) →
      ∀ T : OAI.Analysis.Normed.Function.Holder.HolderMap K (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) →
      ∃ Q : OAI.Analysis.Normed.Function.Holder.HolderMap (e ⁻¹' closure S) (X →L[ℝ] X →L[ℝ] X →L[ℝ] ℝ) α,
        ‖Q‖ ≤ A*(1+‖U‖+‖T‖) ∧ ∀ x : e ⁻¹' closure S,
          OAI.Analysis.Normed.Function.Holder.HolderMap.value Q x = fderiv ℝ (fderiv ℝ (fderiv ℝ
            (((fun z => u z-B₀ z) ∘ G) ∘ e))) x := by
  obtain ⟨A,hA,hforward⟩ := exists_uniform_subtracted_chart_third_holder hΩK hS hconv
    hcompact hdiam hG hGK hGΩ B₀ hB₀ hα hα1
  refine ⟨A,hA,?_⟩
  intro u hu U hU₁ hU₂ T hT
  obtain ⟨Q,hQ,hQn⟩ := hforward U u (hu.of_le (by norm_num)) hU₁ hU₂ T hT
  obtain ⟨Qf,hQfn,hQf⟩ := OAI.Analysis.PDE.Schauder.exists_third_holder_isometry e hα
    ((fun z => u z-B₀ z) ∘ G) ((hu.sub hB₀).comp hG) Q hQ
  exact ⟨Qf,hQfn.trans hQn,hQf⟩

theorem small_halfball_subset_chart_closure (e : X ≃ₗᵢ[ℝ] E) (k : Fin m)
    {S : Set E} (hinclude : closedCoordinateHalfPatch k 0 (1/2) ⊆ e ⁻¹' closure S)
    {δ : ℝ} (hδ : δ ≤ 1/2) :
    ball (0 : E) δ ∩ {z | 0 ≤ e.symm z k} ⊆ closure S := by
  intro z hz
  have hb : e.symm z ∈ closedCoordinateHalfPatch k 0 (1/2) := by
    refine ⟨?_, hz.2⟩
    have hn : ‖z‖ < δ := by simpa only [mem_ball, dist_zero_right] using hz.1
    simpa only [mem_closedBall, dist_zero_right, e.symm.norm_map] using hn.le.trans hδ
  simpa only [mem_preimage, e.apply_symm_apply] using hinclude hb

theorem restrict_third_lower_jets {S K : Set E} (hSK : S ⊆ K)
    {u : E → ℝ} {α M : ℝ} (h : OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn u K α M) :
    OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn u S α M :=
  ⟨fun x hx => h.value x (hSK hx), fun x hx => h.first x (hSK hx),
    fun x hx => h.second x (hSK hx),
    fun x hx y hy => h.value_sub x (hSK hx) y (hSK hy),
    fun x hx y hy => h.first_sub x (hSK hx) y (hSK hy),
    fun x hx y hy => h.second_sub x (hSK hx) y (hSK hy)⟩

theorem exists_flat_to_physical_third_return (e : X ≃ₗᵢ[ℝ] E) (k : Fin m)
    (r : E → ℝ) (hr : Continuous r) (a : E) (hra : r a = 0)
    {S : Set E} (hinclude : closedCoordinateHalfPatch k 0 (1/2) ⊆ e ⁻¹' closure S)
    (G P : E → E) (hG : ContDiff ℝ 4 G) (hP : ContDiff ℝ 4 P)
    (hG0 : G 0 = a) (hinv0 : (fun z => P (G z)) =ᶠ[𝓝 (0 : E)] id)
    {c : ℝ} (hc : 0 < c)
    (hlevel : ∀ z ∈ closedBall 0 2, r (G z)-r a = -c*(e.symm z) k)
    (B₀ : E → ℝ) (hB₀ : ContDiff ℝ 4 B₀)
    {α δ₀ : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hδ₀ : 0 < δ₀) :
    ∃ ρ > 0, ∃ C > 0, ∀ u : E → ℝ, ContDiff ℝ 3 u →
      ∀ V M : ℝ, 0 ≤ V → 0 ≤ M →
      OAI.Analysis.PDE.Dirichlet.C2JetHolderBoundsOn (fun z => u (G z)-B₀ (G z)) (closure S) α V →
      ThirdDerivativeBound (((fun z => u z-B₀ z) ∘ G) ∘ e)
        (ball 0 δ₀ ∩ {z | 0 ≤ z k}) α M →
      ThirdDerivativeBound u (closedBall a ρ ∩ {x | r x ≤ 0}) α (C*(1+V+M)) := by
  let δ := min δ₀ (1/2)
  have hδ : 0 < δ := lt_min hδ₀ (by norm_num)
  have hsub := small_halfball_subset_chart_closure e k hinclude (min_le_right δ₀ (1/2))
  obtain ⟨ρ,hρ,C,hC,hreturn⟩ := exists_physical_third_return hc hr hP hG hG0
    hinv0 hlevel hra B₀ hB₀ hα hα1 hδ
  refine ⟨ρ,hρ,C,hC,?_⟩
  intro u hu V M hV hM hlo hflat
  let v : E → ℝ := fun z => u (G z)-B₀ (G z)
  have hv : ContDiff ℝ 3 v := (hu.sub (hB₀.of_le (by norm_num))).comp (hG.of_le (by norm_num))
  obtain ⟨hn,hh⟩ := third_halfball_estimate_isometry_return e k v hv
    (fun x hx hk => hflat.1 x ⟨hx,hk⟩)
    (fun x hx hk y hy hj => hflat.2 x ⟨hx,hk⟩ y ⟨hy,hj⟩)
  obtain ⟨hpn,hph⟩ := hreturn u hu V M hV hM (restrict_third_lower_jets hsub hlo)
    (fun z hz => hn z (ball_subset_ball (min_le_left δ₀ (1/2)) hz.1) hz.2)
    (fun z hz w hw => hh z (ball_subset_ball (min_le_left δ₀ (1/2)) hz.1) hz.2
      w (ball_subset_ball (min_le_left δ₀ (1/2)) hw.1) hw.2)
  exact ⟨fun x hx => hpn x hx.1 hx.2, fun x hx y hy => hph x hx.1 hx.2 y hy.1 hy.2⟩

theorem nonlinear_physical_boundary_third_estimate
    (hm : 3 ≤ m) (e : X ≃ₗᵢ[ℝ] E) (k : Fin m)
    (r : E → ℝ) (hr : Continuous r) (a : E) (hra : r a = 0)
    (hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0})
    {S : Set E} (hS : IsOpen S) (hconv : Convex ℝ S)
    (hcompact : IsCompact (closure S))
    (hdiam : ∀ x ∈ closure S, ∀ y ∈ closure S, ‖x-y‖ ≤ 1)
    (hinclude : closedCoordinateHalfPatch k 0 (1/2) ⊆ e ⁻¹' closure S)
    (hinterior : ∀ x ∈ ball (0 : X) (1/8), 0 < x k → e x ∈ S)
    (G P : E → E) (hG : ContDiff ℝ 4 G) (hP : ContDiff ℝ 4 P)
    (hG0 : G 0 = a) (hinv0 : (fun z => P (G z)) =ᶠ[𝓝 (0 : E)] id)
    (hGK : MapsTo G (closure S) {x | r x ≤ 0}) (hGΩ : MapsTo G S {x | r x < 0})
    (hinv : ∀ x ∈ closure S, (fun z => P (G z)) =ᶠ[𝓝 x] id)
    {c : ℝ} (hc : 0 < c)
    (hlevel : ∀ z ∈ closedBall 0 2, r (G z)-r a = -c*(e.symm z) k)
    (B₀ : E → ℝ) (hB₀ : ContDiff ℝ 4 B₀)
    {α R N Z ell Λ : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hR : 0 ≤ R) (hN : 0 ≤ N) (hZ : 0 ≤ Z) (hell : 0 < ell) (hΛ : 0 ≤ Λ) :
    ∃ ρ > 0, ∀ ε > 0, ∃ D > 0,
      ∀ p : BoundaryLogSolution e k hΩK S G B₀ α R N Z ell Λ,
      ∀ T : OAI.Analysis.Normed.Function.Holder.HolderMap {x | r x ≤ 0} (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      (∀ x : {x | r x ≤ 0}, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ p.u)) x) →
      (∀ x ∈ closedBall a ρ, r x ≤ 0 →
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ p.u)) x‖ ≤ ε*‖T‖+D) ∧
      (∀ x ∈ closedBall a ρ, r x ≤ 0 → ∀ y ∈ closedBall a ρ, r y ≤ 0 →
        ‖fderiv ℝ (fderiv ℝ (fderiv ℝ p.u)) x-fderiv ℝ (fderiv ℝ (fderiv ℝ p.u)) y‖ ≤
          (ε*‖T‖+D)*‖x-y‖^α) := by
  obtain ⟨V, hV, hlower⟩ := exists_chart_remainder_jet_bound G (hG.of_le (by norm_num))
    B₀ (hB₀.of_le (by norm_num)) hcompact hconv.closure hGK hα.le hα1.le hR
  obtain ⟨A, hA, hforward⟩ := exists_uniform_subtracted_flat_holder e hΩK hS hconv
    hcompact hdiam G hG hGK hGΩ B₀ hB₀ hα.le hα1.le
  obtain ⟨δ₀, hδ₀, hflat⟩ := nonlinear_boundary_third_estimate hm e k hΩK
    (isOpen_lt hr continuous_const) hS hconv hcompact hdiam hinclude hinterior
    G P hG hP hGK hGΩ hinv B₀ hB₀ hα hα1 hR hN hZ hell hΛ
  obtain ⟨ρ,hρ,C,hC,hreturn⟩ := exists_flat_to_physical_third_return e k r hr a hra
    hinclude G P hG hP hG0 hinv0 hc hlevel B₀ hB₀ hα.le hα1.le hδ₀
  refine ⟨ρ, hρ, ?_⟩
  intro ε hε
  let μ := ε/(C*A)
  have hμ : 0 < μ := by positivity
  obtain ⟨D₀, hD₀, hestimate⟩ := hflat μ hμ
  let D := C*(1+V+μ*A*(1+R)+D₀)
  refine ⟨D, by dsimp only [D]; positivity, ?_⟩
  intro p T hT
  obtain ⟨Qf, hQn, hQf⟩ := hforward p.u p.smooth p.U
    p.first_U p.second_U T hT
  obtain ⟨hn, hh⟩ := hestimate p Qf hQf
  let M := μ*‖Qf‖+D₀
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hlo := hlower p.u (p.smooth.of_le (by norm_num)) p.U p.norm_U
    p.value_U p.first_U p.second_U
  have hp := hreturn p.u (p.smooth.of_le (by norm_num)) V M hV.le hM hlo
    ⟨fun x hx => hn x hx.1 hx.2, fun x hx y hy => hh x hx.1 hx.2 y hy.1 hy.2⟩
  have hQbound : ‖Qf‖ ≤ A*(1+R+‖T‖) := hQn.trans (by gcongr; exact p.norm_U)
  have hbound : C*(1+V+M) ≤ ε*‖T‖+D := third_return_small_error hC hA hε hQbound
  have hfinal := hp.mono hbound
  exact ⟨fun x hx hrx => hfinal.1 x ⟨hx,hrx⟩,
    fun x hx hrx y hy hry => hfinal.2 x ⟨hx,hrx⟩ y ⟨hy,hry⟩⟩

end OAI.Analysis.PDE.Elliptic
