import OAI.Geometry.ComplexTorus.RiemannProjectivity.LocalBounded
import OAI.Geometry.ComplexTorus.RiemannProjectivity.HolomorphicZero
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.LinearImmersionComplement

/-! # Removable Global -/

namespace OAI

noncomputable section

namespace Geometry.ComplexTorus.RiemannProjectivity.RemovableGlobal.Constructions.RemovableHypersurface

/-!
# RiemannProjectivity: local bounded removability for a holomorphic hypersurface

A nonflat holomorphic germ is nonzero on some complex line. Linear normal
coordinates put that line in the vertical direction of the Cauchy extension
theorem, giving local extension in arbitrary finite complex dimension.
-/

open Set Filter _root_.Metric
open scoped _root_.Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

theorem coordinates_along_vector {v : V} (hv : v ≠ 0) :
    ∃ (n : ℕ) (e : ((Fin n → ℂ) × ℂ) ≃L[ℂ] V), ∀ z : ℂ, e (0, z) = z • v := by
  let L : ℂ →L[ℂ] V := (ContinuousLinearMap.id ℂ ℂ).smulRight v
  have hL : Function.Injective L := by
    intro a b hab
    change a • v = b • v at hab
    have h : (a - b) • v = 0 := by rw [sub_smul, hab, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_right hv)
  obtain ⟨K, e₀, he₀⟩ := AlgebraicGeometry.ComplexPoints.Analytic.LinearImmersionComplement.exists_linearImmersionComplement L hL
  let b := (Module.finBasis ℂ K).equivFunL.symm
  let e := (ContinuousLinearEquiv.prodComm ℂ (Fin (Module.finrank ℂ K) → ℂ) ℂ).trans
    (((ContinuousLinearEquiv.refl ℂ ℂ).prodCongr b).trans e₀)
  refine ⟨Module.finrank ℂ K, e, ?_⟩
  intro z
  change e₀ (z, b 0) = z • v
  rw [map_zero, he₀]
  simp only [Submodule.coe_zero, add_zero]
  rfl

theorem exists_local_bounded_extension {f g : V → ℂ} {O : Set V}
    (hO : IsOpen O) (hg : DifferentiableOn ℂ g O)
    (hf : DifferentiableOn ℂ f (O ∩ {p | g p ≠ 0})) {x : V} (hx : x ∈ O)
    (hn : ¬∀ᶠ y in 𝓝 x, g y = 0) {C : ℝ}
    (hbound : ∀ p ∈ O ∩ {p | g p ≠ 0}, ‖f p‖ ≤ C) :
    ∃ (U : Set V) (H : V → ℂ), IsOpen U ∧ x ∈ U ∧ U ⊆ O ∧
      DifferentiableOn ℂ H U ∧ EqOn H f (U ∩ {p | g p ≠ 0}) ∧ ∀ p ∈ U, ‖H p‖ ≤ C := by
  by_cases hgx : g x ≠ 0
  · exact ⟨O ∩ {p | g p ≠ 0}, f,
      hg.continuousOn.isOpen_inter_preimage hO isOpen_compl_singleton,
      ⟨hx, hgx⟩, inter_subset_left, hf, fun _ _ => rfl, hbound⟩
  · have hgx0 : g x = 0 := not_not.mp hgx
    obtain ⟨v, _, hvline⟩ := HolomorphicZero.Constructions.HolomorphicZeroDimension.exists_nonzero_line_in_dense_directions
      hO hg hx hn dense_univ
    have hv : v ≠ 0 := by
      intro hv0
      apply hvline
      exact Filter.Eventually.of_forall (fun z => by simp only [hv0, smul_zero, add_zero, hgx0])
    obtain ⟨n, e, he⟩ := coordinates_along_vector hv
    let a : ((Fin n → ℂ) × ℂ) ≃ₜ V := e.toHomeomorph.trans (Homeomorph.addLeft x)
    have ha (p : (Fin n → ℂ) × ℂ) : a p = x + e p := rfl
    have hasym (y : V) : a.symm y = e.symm (y - x) := by
      change e.symm (-x + y) = e.symm (y - x)
      rw [sub_eq_add_neg, add_comm]
    have had : Differentiable ℂ a := (differentiable_const x).add e.differentiable
    have haid : Differentiable ℂ a.symm := by
      have hfun : (fun y => a.symm y) = fun y => e.symm (y - x) := funext hasym
      change Differentiable ℂ (fun y => a.symm y)
      rw [hfun]
      exact e.symm.differentiable.comp (differentiable_id.sub_const x)
    have ha0 : a (0, 0) = x := by rw [ha]; simp
    let O' := a ⁻¹' O
    have hO' : IsOpen O' := hO.preimage a.continuous
    have hg' : DifferentiableOn ℂ (g ∘ a) O' :=
      hg.comp had.differentiableOn (mapsTo_preimage a O)
    have hf' : DifferentiableOn ℂ (f ∘ a) (O' ∩ {p | (g ∘ a) p ≠ 0}) :=
      hf.comp had.differentiableOn (fun _ hp => hp)
    have hx' : ((0 : Fin n → ℂ), (0 : ℂ)) ∈ O' := by
      change a (0, 0) ∈ O
      rwa [ha0]
    have hn' : ¬∀ᶠ z in 𝓝 (0 : ℂ), (g ∘ a) (0, z) = 0 := by
      simpa only [Function.comp_apply, ha, he] using hvline
    obtain ⟨B, H, hB, h0B, hBO, hH, hHeq, hHb⟩ :=
      LocalBounded.Constructions.LocalBoundedExtension.exists_extension_of_vertical_germ hO' hg' hf' hx' hn'
        (fun p hp => hbound (a p) hp)
    refine ⟨a.symm ⁻¹' B, H ∘ a.symm, hB.preimage a.symm.continuous, ?_, ?_,
      hH.comp haid.differentiableOn (mapsTo_preimage a.symm B), ?_, ?_⟩
    · change a.symm x ∈ B
      rw [← ha0, a.symm_apply_apply]
      exact h0B
    · intro y hy
      have h := hBO hy
      change a (a.symm y) ∈ O at h
      simpa only [a.apply_symm_apply] using h
    · intro y hy
      have hnonzero : (g ∘ a) (a.symm y) ≠ 0 := by
        simpa only [Function.comp_apply, a.apply_symm_apply] using (show g y ≠ 0 from hy.2)
      have h := hHeq ⟨hy.1, hnonzero⟩
      simpa only [Function.comp_apply, a.apply_symm_apply] using h
    · intro y hy
      exact hHb (a.symm y) hy

end Geometry.ComplexTorus.RiemannProjectivity.RemovableGlobal.Constructions.RemovableHypersurface

namespace Geometry.ComplexTorus.RiemannProjectivity.RemovableGlobal.Constructions.GlobalRemovability

/-!
# RiemannProjectivity: gluing bounded holomorphic extensions

The nonzero locus of a nonflat holomorphic function is dense. Local
extensions agree there and hence agree at every overlap point by continuity.
They glue to an entire function and preserve any continuous pointwise bound.
-/

open Set Filter _root_.Metric
open scoped _root_.Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

omit [NormedSpace ℂ V] [FiniteDimensional ℂ V] in
theorem dense_nonzero_of_nonflat {g : V → ℂ}
    (hn : ∀ x, ¬∀ᶠ z in 𝓝 x, g z = 0) : Dense {z | g z ≠ 0} := by
  intro x
  apply mem_closure_iff_frequently.mpr
  simpa only [mem_ofPred_eq, Filter.Frequently, not_not] using hn x

omit [NormedSpace ℂ V] [FiniteDimensional ℂ V] in
theorem eq_at_of_nonflat {g H J : V → ℂ} {x : V}
    (hn : ¬∀ᶠ z in 𝓝 x, g z = 0) (hH : ContinuousAt H x) (hJ : ContinuousAt J x)
    (heq : ∀ᶠ z in 𝓝 x, g z ≠ 0 → H z = J z) : H x = J x := by
  have hfreq : ∃ᶠ z in 𝓝 x, g z ≠ 0 := by
    simpa only [Filter.Frequently, not_not] using hn
  exact tendsto_nhds_unique_of_frequently_eq hH hJ
    ((hfreq.and_eventually heq).mono (fun z hz => hz.2 hz.1))

theorem exists_entire_extension {f g : V → ℂ} (hg : Differentiable ℂ g)
    (hf : ∀ x, g x ≠ 0 → DifferentiableAt ℂ f x)
    (hn : ∀ x, ¬∀ᶠ z in 𝓝 x, g z = 0)
    (hb : ∀ x : V, ∃ (r C : ℝ), 0 < r ∧ ∀ z ∈ ball x r, g z ≠ 0 → ‖f z‖ ≤ C) :
    ∃ F : V → ℂ, Differentiable ℂ F ∧ ∀ x, g x ≠ 0 → F x = f x := by
  classical
  have hlocal (x : V) : ∃ (U : Set V) (H : V → ℂ), IsOpen U ∧ x ∈ U ∧
      DifferentiableOn ℂ H U ∧ EqOn H f (U ∩ {p | g p ≠ 0}) := by
    obtain ⟨r, C, hr, hbound⟩ := hb x
    obtain ⟨U, H, hU, hx, _, hH, hHeq, _⟩ :=
      RemovableHypersurface.exists_local_bounded_extension isOpen_ball hg.differentiableOn
        (fun z hz => (hf z hz.2).differentiableWithinAt) (mem_ball_self hr) (hn x)
        (fun z hz => hbound z hz.1 hz.2)
    exact ⟨U, H, hU, hx, hH, hHeq⟩
  choose U H hU hxU hH hHeq using hlocal
  let F : V → ℂ := fun x => H x x
  have hF_eq (x : V) : F =ᶠ[𝓝 x] H x := by
    filter_upwards [(hU x).mem_nhds (hxU x)] with z hz
    apply eq_at_of_nonflat (hn z)
      (((hH z).differentiableAt ((hU z).mem_nhds (hxU z))).continuousAt)
      (((hH x).differentiableAt ((hU x).mem_nhds hz)).continuousAt)
    filter_upwards [(hU z).mem_nhds (hxU z), (hU x).mem_nhds hz] with w hwz hwx hgw
    exact (hHeq z ⟨hwz, hgw⟩).trans (hHeq x ⟨hwx, hgw⟩).symm
  exact ⟨F, fun x => ((hH x).differentiableAt ((hU x).mem_nhds (hxU x))).congr_of_eventuallyEq
    (hF_eq x), fun x hx => hHeq x ⟨hxU x, hx⟩⟩

omit [FiniteDimensional ℂ V] in
theorem bound_entire_extension {f g F : V → ℂ}
    (hF : Differentiable ℂ F) (heq : ∀ x, g x ≠ 0 → F x = f x)
    (hn : ∀ x, ¬∀ᶠ z in 𝓝 x, g z = 0) {B : V → ℝ} (hB : Continuous B)
    (hbound : ∀ x, g x ≠ 0 → ‖f x‖ ≤ B x) : ∀ x, ‖F x‖ ≤ B x := by
  intro x
  apply (dense_nonzero_of_nonflat hn).induction (P := fun z => ‖F z‖ ≤ B z) ?_ ?_ x
  · intro x hx
    rw [heq x hx]
    exact hbound x hx
  · exact isClosed_le hF.continuous.norm hB

omit [FiniteDimensional ℂ V] in
theorem nonflat_of_entire_nonzero {g : V → ℂ} (hg : Differentiable ℂ g)
    (hne : ∃ y, g y ≠ 0) (x : V) : ¬∀ᶠ z in 𝓝 x, g z = 0 := by
  intro hx
  obtain ⟨y, hy⟩ := hne
  exact hy (IdentityEq.Constructions.Identity.eq_zero_of_zero_germ isOpen_univ isPreconnected_univ hg.differentiableOn
    (mem_univ x) hx y (mem_univ y))

theorem exists_entire_extension_of_continuous_bound {f g : V → ℂ}
    (hg : Differentiable ℂ g) (hne : ∃ y, g y ≠ 0)
    (hf : ∀ x, g x ≠ 0 → DifferentiableAt ℂ f x) {B : V → ℝ} (hB : Continuous B)
    (hbound : ∀ x, g x ≠ 0 → ‖f x‖ ≤ B x) :
    ∃ F : V → ℂ, Differentiable ℂ F ∧ (∀ x, g x ≠ 0 → F x = f x) ∧
      ∀ x, ‖F x‖ ≤ B x := by
  let : ProperSpace V := FiniteDimensional.proper ℂ V
  have hn := nonflat_of_entire_nonzero hg hne
  have hb : ∀ x : V, ∃ (r C : ℝ), 0 < r ∧ ∀ z ∈ ball x r, g z ≠ 0 → ‖f z‖ ≤ C := by
    intro x
    obtain ⟨D, hD⟩ := (isCompact_closedBall x 1).exists_bound_of_continuousOn hB.continuousOn
    refine ⟨1, D, zero_lt_one, ?_⟩
    intro z hz hgz
    exact (hbound z hgz).trans ((le_abs_self _).trans (hD z (ball_subset_closedBall hz)))
  obtain ⟨F, hF, heq⟩ := exists_entire_extension hg hf hn hb
  exact ⟨F, hF, heq, bound_entire_extension hF heq hn hB hbound⟩

end Geometry.ComplexTorus.RiemannProjectivity.RemovableGlobal.Constructions.GlobalRemovability

end

end OAI
