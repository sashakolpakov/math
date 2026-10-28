import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.BoundedQuotient
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.GenericDegree
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LocalPreparation
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ParametricIntegralAt

/-! # Quotient -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Quotient.Constructions.Removable

noncomputable section

section

/-!
# Extension of bounded holomorphic quotients in several variables

A complex line on which the denominator is not identically zero gives a
small circle avoiding its zeros. Cauchy integration on its nearby translates
then gives a holomorphic extension of the bounded quotient.
-/

open Set Filter _root_.Metric _root_.Complex
open scoped _root_.Topology

theorem exists_transverse_disk {n : ℕ} {g : (Fin n → ℂ) → ℂ}
    {U : Set (Fin n → ℂ)} (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    {x : Fin n → ℂ} (hx : x ∈ U) (hn : ¬∀ᶠ y in 𝓝 x, g y = 0) :
    ∃ (v : Fin n → ℂ) (r : ℝ), 0 < r ∧
      (∀ z ∈ closedBall (0 : ℂ) r, x + z • v ∈ U) ∧
      ∀ z ∈ sphere (0 : ℂ) r, g (x + z • v) ≠ 0 := by
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  obtain ⟨y, hgy, hy⟩ := ((not_eventually.mp hn).and_eventually
    (ball_mem_nhds x (show 0 < R / 4 by linarith))).exists
  let v := y - x
  let line : ℂ → (Fin n → ℂ) := fun z => x + z • v
  have hline : Differentiable ℂ line :=
    (differentiable_const x).add (differentiable_id.smul_const v)
  have hmaps : MapsTo line (ball (0 : ℂ) 2) U := by
    intro z hz
    apply hball
    rw [mem_ball_iff_norm]
    change ‖x + z • v - x‖ < R
    rw [add_sub_cancel_left, norm_smul]
    have hz2 : ‖z‖ < 2 := by simpa only [mem_ball_iff_norm, sub_zero] using hz
    have hv : ‖v‖ < R / 4 := mem_ball_iff_norm.mp hy
    calc
      ‖z‖ * ‖v‖ ≤ 2 * ‖v‖ := mul_le_mul_of_nonneg_right hz2.le (norm_nonneg _)
      _ < R := by linarith
  have hlineG : DifferentiableOn ℂ (fun z => g (line z)) (ball (0 : ℂ) 2) :=
    hg.comp hline.differentiableOn hmaps
  have hlineN : ¬∀ᶠ z in 𝓝 (0 : ℂ), g (line z) = 0 := by
    intro hz
    have hi := HolomorphicIdentity.Constructions.Identity.eqOn_zero_ball_of_eventually_zero hlineG hz
      (show (1 : ℂ) ∈ ball 0 2 by norm_num)
    apply hgy
    simpa only [line, v, one_smul, ← add_sub_assoc, add_sub_cancel_left, Pi.zero_apply] using hi
  let F : (Fin n → ℂ) × ℂ → ℂ := fun p => g (p.1 + p.2 • v)
  let W : Set ((Fin n → ℂ) × ℂ) := (fun p => p.1 + p.2 • v) ⁻¹' U
  have hmap : Differentiable ℂ (fun p : (Fin n → ℂ) × ℂ => p.1 + p.2 • v) :=
    differentiable_fst.add (differentiable_snd.smul_const v)
  have hW : IsOpen W := hU.preimage hmap.continuous
  have hF : DifferentiableOn ℂ F W := hg.comp hmap.differentiableOn (fun _ hp => hp)
  have hbase : (x, (0 : ℂ)) ∈ W := by simpa only [W, mem_preimage, zero_smul, add_zero] using hx
  obtain ⟨r, hr, hbaseR, hboundary⟩ := LocalPreparation.Constructions.Preparation.exists_zero_free_circle hW hF hbase hlineN
  exact ⟨v, r, hr, hbaseR, hboundary⟩

theorem exists_holomorphic_quotient_extension {n : ℕ}
    {f g : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U)
    {x : Fin n → ℂ} (hx : x ∈ U) (hn : ¬∀ᶠ y in 𝓝 x, g y = 0)
    (hbound : ∃ M : ℝ, ∀ y ∈ U, g y ≠ 0 → ‖f y / g y‖ ≤ M) :
    ∃ (V : Set (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ DifferentiableOn ℂ F V ∧
      ∀ y ∈ V, g y ≠ 0 → F y = f y / g y := by
  obtain ⟨v, R, hR, hbase, hboundary⟩ := exists_transverse_disk hU hg hx hn
  let line : (Fin n → ℂ) × ℂ → (Fin n → ℂ) := fun p => p.1 + p.2 • v
  have hline : Differentiable ℂ line :=
    differentiable_fst.add (differentiable_snd.smul_const v)
  let W := line ⁻¹' U
  have hW : IsOpen W := hU.preimage hline.continuous
  have hfW : DifferentiableOn ℂ (f ∘ line) W := hf.comp hline.differentiableOn (fun _ hp => hp)
  have hgW : DifferentiableOn ℂ (g ∘ line) W := hg.comp hline.differentiableOn (fun _ hp => hp)
  obtain ⟨V, hV, hxV, hVW, hVboundary⟩ :=
    RootFamiliesAt.Constructions.RootFamilies.exists_disk_family_neighborhood hW hgW.continuousOn hbase hboundary
  let W' := W ∩ (g ∘ line) ⁻¹' ({0} : Set ℂ)ᶜ
  have hW' : IsOpen W' :=
    hgW.continuousOn.isOpen_inter_preimage hW isClosed_singleton.isOpen_compl
  let Q : (Fin n → ℂ) × ℂ → ℂ := fun p => f (line p) / g (line p)
  have hQ : DifferentiableOn ℂ Q W' := by
    change DifferentiableOn ℂ (fun p => (f ∘ line) p / (g ∘ line) p) W'
    simp only [div_eq_mul_inv]
    exact (hfW.mono (show W' ⊆ W from inter_subset_left)).fun_mul
      ((hgW.mono inter_subset_left).fun_inv (fun p (hp : p ∈ W') => hp.2))
  have hVW' : V ×ˢ sphere (0 : ℂ) R ⊆ W' := fun p hp =>
    ⟨hVW ⟨hp.1, sphere_subset_closedBall hp.2⟩, hVboundary p hp⟩
  have hw : ContinuousOn (fun z : ℂ => z⁻¹) (sphere 0 R) := by
    apply continuous_id.continuousOn.inv₀
    intro z hz hz0
    change z = 0 at hz0
    have hnorm : ‖z‖ = R := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    rw [hz0, norm_zero] at hnorm
    exact hR.ne' hnorm.symm
  let F : (Fin n → ℂ) → ℂ := fun y => (2 * Real.pi * I : ℂ)⁻¹ *
    ∮ z in C(0, R), z⁻¹ * Q (y, z)
  have hVU : V ⊆ U := by
    intro y hy
    have h := hVW (show (y, (0 : ℂ)) ∈ V ×ˢ closedBall 0 R from
      ⟨hy, mem_closedBall_self hR.le⟩)
    simpa only [W, line, mem_preimage, zero_smul, add_zero] using h
  refine ⟨V, F, hV, hxV, hVU, ?_, ?_⟩
  · intro y hy
    exact ((ParametricIntegralAt.Constructions.ParametricIntegral.differentiableAt_weighted_circleIntegral hW' hQ hV hy
      hR.le hVW' hw).const_mul _).differentiableWithinAt
  · intro y hy hgy
    let Uy : Set ℂ := (fun z : ℂ => y + z • v) ⁻¹' U
    have hly : Differentiable ℂ (fun z : ℂ => y + z • v) :=
      (differentiable_const y).add (differentiable_id.smul_const v)
    have hUy : IsOpen Uy := hU.preimage hly.continuous
    have hfUy : AnalyticOnNhd ℂ (fun z : ℂ => f (y + z • v)) Uy :=
      (hf.comp hly.differentiableOn (fun _ hp => hp)).analyticOnNhd hUy
    have hgUy : AnalyticOnNhd ℂ (fun z : ℂ => g (y + z • v)) Uy :=
      (hg.comp hly.differentiableOn (fun _ hp => hp)).analyticOnNhd hUy
    obtain ⟨M, hM⟩ := hbound
    have hquot := BoundedQuotient.Constructions.Removable.quotient_eq_circleIntegral hUy hfUy hgUy
      ⟨M, fun z hz => hM (y + z • v) hz⟩ hR
      (fun z hz => hVW (show (y, z) ∈ V ×ˢ closedBall 0 R from ⟨hy, hz⟩))
      (fun z hz => hVboundary (y, z) ⟨hy, hz⟩)
      (by simpa only [zero_smul, add_zero] using hgy)
    simpa only [F, Q, line, sub_zero, zero_smul, add_zero] using hquot

end

/-!
# Bounded holomorphic functions extend across a holomorphic zero set

Multiply by the square of a defining function, extend that product by zero,
and apply the bounded-quotient extension theorem.
-/

open Set Filter _root_.Metric _root_.Complex Asymptotics
open scoped _root_.Topology

theorem hasFDerivAt_mul_sq_of_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f g : E → ℂ} {x : E} (hg : DifferentiableAt ℂ g x) (hgx : g x = 0)
    (hbound : ∃ M : ℝ, ∀ᶠ y in 𝓝 x, ‖f y‖ ≤ M) :
    HasFDerivAt (fun y => f y * (g y) ^ 2) (0 : E →L[ℂ] ℂ) x := by
  obtain ⟨M, hM⟩ := hbound
  have hfO : f =O[𝓝 x] (fun _ : E => (1 : ℝ)) :=
    IsBigO.of_bound M (by simpa only [norm_one, mul_one] using hM)
  have hgo : g =o[𝓝 x] (fun _ : E => (1 : ℝ)) :=
    (isLittleO_one_iff ℝ).mpr (by simpa only [hgx] using hg.continuousAt.tendsto)
  have hgO : g =O[𝓝 x] (fun y => ‖y - x‖) := by
    simpa only [hgx, sub_zero] using hg.isBigO_sub.norm_right
  have hsmall : (fun y => f y * g y * g y) =o[𝓝 x] (fun y => y - x) := by
    apply IsLittleO.of_norm_right
    simpa only [one_mul] using (hfO.mul_isLittleO hgo).mul_isBigO hgO
  apply HasFDerivAt.of_isLittleO
  simpa only [hgx, zero_pow (by omega : 2 ≠ 0), mul_zero, sub_zero,
    zero_apply, pow_two, mul_assoc] using hsmall

theorem exists_extension_off_zero_set {n : ℕ}
    {f g : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)}
    (hU : IsOpen U) (hg : DifferentiableOn ℂ g U)
    (hf : DifferentiableOn ℂ f {y | y ∈ U ∧ g y ≠ 0})
    {x : Fin n → ℂ} (hx : x ∈ U) (hn : ¬∀ᶠ y in 𝓝 x, g y = 0)
    (hbound : ∃ M : ℝ, ∀ y ∈ U, g y ≠ 0 → ‖f y‖ ≤ M) :
    ∃ (V : Set (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ DifferentiableOn ℂ F V ∧
      ∀ y ∈ V, g y ≠ 0 → F y = f y := by
  classical
  let f₀ : (Fin n → ℂ) → ℂ := fun y => if g y = 0 then 0 else f y
  let H : (Fin n → ℂ) → ℂ := fun y => f₀ y * (g y) ^ 2
  obtain ⟨M, hM⟩ := hbound
  have hf₀bound (y : Fin n → ℂ) (hy : y ∈ U) : ‖f₀ y‖ ≤ max 0 M := by
    by_cases hgy : g y = 0
    · simpa only [f₀, ite_eq_left hgy, norm_zero] using (le_max_left (0 : ℝ) M)
    · exact (show ‖f₀ y‖ ≤ M by simpa only [f₀, ite_eq_right hgy] using hM y hy hgy).trans
        (le_max_right _ _)
  have hgood : IsOpen {y | y ∈ U ∧ g y ≠ 0} :=
    hg.continuousOn.isOpen_inter_preimage hU isClosed_singleton.isOpen_compl
  have hH : DifferentiableOn ℂ H U := by
    intro y hy
    have hgy := hg.differentiableAt (hU.mem_nhds hy)
    by_cases hzero : g y = 0
    · apply (hasFDerivAt_mul_sq_of_bounded hgy hzero ?_).differentiableAt.differentiableWithinAt
      refine ⟨max 0 M, ?_⟩
      filter_upwards [hU.mem_nhds hy] with z hz
      exact hf₀bound z hz
    · have hf₀eq : f₀ =ᶠ[𝓝 y] f := by
        filter_upwards [hgy.continuousAt.eventually_ne hzero] with z hz
        exact ite_eq_right hz
      have hf₀y : DifferentiableAt ℂ f₀ y :=
        (hf.differentiableAt (hgood.mem_nhds ⟨hy, hzero⟩)).congr_of_eventuallyEq hf₀eq
      exact (hf₀y.mul (hgy.pow 2)).differentiableWithinAt
  have hg₂ : DifferentiableOn ℂ (fun y => (g y) ^ 2) U := hg.pow 2
  have hg₂n : ¬∀ᶠ y in 𝓝 x, (g y) ^ 2 = 0 := by
    intro hz
    apply hn
    exact hz.mono (fun _ h => (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp h)
  have hquotBound : ∃ C : ℝ, ∀ y ∈ U, (g y) ^ 2 ≠ 0 → ‖H y / (g y) ^ 2‖ ≤ C := by
    refine ⟨max 0 M, ?_⟩
    intro y hy hgy
    change ‖(f₀ y * (g y) ^ 2) / (g y) ^ 2‖ ≤ _
    rw [mul_div_cancel_right₀ _ hgy]
    exact hf₀bound y hy
  obtain ⟨V, F, hV, hxV, hVU, hF, hFeq⟩ :=
    exists_holomorphic_quotient_extension hU hH hg₂ hx hg₂n hquotBound
  refine ⟨V, F, hV, hxV, hVU, hF, ?_⟩
  intro y hy hgy
  rw [hFeq y hy (pow_ne_zero 2 hgy)]
  change (f₀ y * (g y) ^ 2) / (g y) ^ 2 = f y
  rw [mul_div_cancel_right₀ _ (pow_ne_zero 2 hgy)]
  exact ite_eq_right hgy

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.Quotient.Constructions.Removable
