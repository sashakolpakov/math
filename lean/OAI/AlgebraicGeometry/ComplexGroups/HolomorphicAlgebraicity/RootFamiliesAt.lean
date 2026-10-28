import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ClosedDiskFactorization
import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.HolomorphicRegularity

/-! # Root Families At -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.RootFamiliesAt.Constructions.RootFamilies

noncomputable section

/-!
# Root counts in holomorphic families

The normalized zeroth contour moment is a natural number. Joint holomorphy
makes it continuous in the parameter, so it is locally constant as long as
the boundary circle contains no zeros.
-/

open Set Filter _root_.Metric _root_.Complex
open scoped _root_.Topology BigOperators

def moment (f : ℂ → ℂ) (c : ℂ) (R : ℝ) (k : ℕ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ * ∮ z in C(c, R), z ^ k * logDeriv f z

theorem exists_nonzero_in_ball {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : ContinuousOn f (closedBall c R))
    (hboundary : ∀ z ∈ sphere c R, f z ≠ 0) :
    ∃ z ∈ ball c R, f z ≠ 0 := by
  obtain ⟨z, hz⟩ := (NormedSpace.sphere_nonempty (E := ℂ)).mpr hR.le
  have hzc : z ∈ closure (ball c R) := by
    rw [closure_ball c hR.ne']
    exact sphere_subset_closedBall hz
  have hn : {w | f w ≠ 0} ∈ 𝓝[closedBall c R] z :=
    (hf z (sphere_subset_closedBall hz)).eventually_ne (hboundary z hz)
  have hnb : {w | f w ≠ 0} ∈ 𝓝[ball c R] z :=
    nhdsWithin_mono z ball_subset_closedBall hn
  have : NeBot (𝓝[ball c R] z) := mem_closure_iff_nhdsWithin_neBot.mp hzc
  let : NeBot (𝓝[ball c R] z) := this
  obtain ⟨w, hw, hwn⟩ := (eventually_mem_nhdsWithin.and hnb).exists
  exact ⟨w, hw, hwn⟩

theorem exists_moment_root_tuple {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hboundary : ∀ z ∈ sphere c R, f z ≠ 0) :
    ∃ (d : ℕ) (roots : Fin d → ℂ), (∀ i, roots i ∈ ball c R) ∧
      ∀ k : ℕ, moment f c R k = ∑ i, (roots i) ^ k := by
  obtain ⟨d, roots, hr, hm⟩ := ClosedDiskFactorization.Constructions.DiskFactorization.exists_contour_root_moments hR hf
    (exists_nonzero_in_ball hR hf.continuousOn hboundary) hboundary
  refine ⟨d, roots, hr, fun k => ?_⟩
  rw [moment, hm, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]

theorem exists_nat_moment_zero {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hboundary : ∀ z ∈ sphere c R, f z ≠ 0) :
    ∃ d : ℕ, moment f c R 0 = d := by
  obtain ⟨d, roots, _, hm⟩ := exists_moment_root_tuple hR hf hboundary
  exact ⟨d, by simpa using hm 0⟩

theorem nat_eq_of_complex_dist_lt_one {m n : ℕ}
    (h : dist (m : ℂ) (n : ℂ) < 1) : m = n := by
  have hr : |(m : ℝ) - (n : ℝ)| < 1 := by
    simpa only [dist_eq_norm, ← ofReal_natCast, ← ofReal_sub, norm_real,
      Real.norm_eq_abs] using h
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hr
  have hm : m < n + 1 := by exact_mod_cast (by linarith : (m : ℝ) < n + 1)
  have hn : n < m + 1 := by exact_mod_cast (by linarith : (n : ℝ) < m + 1)
  omega

theorem eventually_eq_of_continuousAt_nat_values {X : Type*} [TopologicalSpace X]
    {g : X → ℂ} {x : X} (hg : ContinuousAt g x)
    (hn : ∀ᶠ y in 𝓝 x, ∃ d : ℕ, g y = d) :
    ∀ᶠ y in 𝓝 x, g y = g x := by
  obtain ⟨d, hd⟩ := hn.self_of_nhds
  have hclose : ∀ᶠ y in 𝓝 x, dist (g y) (g x) < 1 :=
    hg (ball_mem_nhds (g x) zero_lt_one)
  filter_upwards [hn, hclose] with y hy hxy
  obtain ⟨e, he⟩ := hy
  rw [he, hd] at hxy ⊢
  exact congrArg (fun a : ℕ => (a : ℂ)) (nat_eq_of_complex_dist_lt_one hxy)

theorem analyticOnNhd_slice {n : ℕ} {F : (Fin n → ℂ) × ℂ → ℂ}
    {W : Set ((Fin n → ℂ) × ℂ)} (hW : IsOpen W)
    (hF : DifferentiableOn ℂ F W) (y : Fin n → ℂ)
    {K : Set ℂ} (hK : ∀ z ∈ K, (y, z) ∈ W) :
    AnalyticOnNhd ℂ (fun z => F (y, z)) K := by
  have hopen : IsOpen ((fun z : ℂ => (y, z)) ⁻¹' W) :=
    hW.preimage (continuous_const.prodMk continuous_id)
  have hd : DifferentiableOn ℂ (fun z => F (y, z)) ((fun z => (y, z)) ⁻¹' W) :=
    hF.comp ((differentiable_const y).prodMk differentiable_id).differentiableOn
      (fun _ hz => hz)
  exact (hd.analyticOnNhd hopen).mono hK

theorem deriv_slice_eq_fderiv {n : ℕ} {F : (Fin n → ℂ) × ℂ → ℂ}
    {p : (Fin n → ℂ) × ℂ} (hF : DifferentiableAt ℂ F p) :
    deriv (fun z => F (p.1, z)) p.2 = fderiv ℂ F p (0, 1) := by
  have hp : HasDerivAt (fun z : ℂ => (p.1, z)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact (hF.hasFDerivAt.comp_hasDerivAt p.2 hp).deriv

theorem continuousAt_moment {n : ℕ} {F : (Fin n → ℂ) × ℂ → ℂ}
    {W : Set ((Fin n → ℂ) × ℂ)} (hW : IsOpen W)
    (hF : DifferentiableOn ℂ F W) {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {x : Fin n → ℂ} (hx : x ∈ U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUW : U ×ˢ sphere c R ⊆ W)
    (hn : ∀ p ∈ U ×ˢ sphere c R, F p ≠ 0) (k : ℕ) :
    ContinuousAt (fun y => moment (fun z => F (y, z)) c R k) x := by
  have hcd := HolomorphicRegularity.Constructions.Regularity.contDiffOn_one_of_differentiableOn_finiteDimensional hW hF
  have hd := (hcd.continuousOn_fderiv_of_isOpen hW le_rfl).clm_apply
    (g := fun _ => ((0 : Fin n → ℂ), (1 : ℂ))) continuousOn_const
  have hl : ContinuousOn (fun p : (Fin n → ℂ) × ℂ =>
      logDeriv (fun z => F (p.1, z)) p.2) (U ×ˢ sphere c R) := by
    apply ((hd.mono hUW).div (hF.continuousOn.mono hUW) hn).congr
    intro p hp
    change deriv (fun z => F (p.1, z)) p.2 / F p = fderiv ℂ F p (0, 1) / F p
    rw [deriv_slice_eq_fderiv (hF.differentiableAt (hW.mem_nhds (hUW hp)))]
  exact (HolomorphicRegularity.Constructions.Regularity.continuousAt_circleIntegral hR hU hx
    ((continuous_snd.pow k).continuousOn.fun_mul hl)).const_mul _

theorem locally_constant_root_count {n : ℕ} {F : (Fin n → ℂ) × ℂ → ℂ}
    {W : Set ((Fin n → ℂ) × ℂ)} (hW : IsOpen W)
    (hF : DifferentiableOn ℂ F W) {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    {x : Fin n → ℂ} (hx : x ∈ U) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hUW : U ×ˢ closedBall c R ⊆ W)
    (hn : ∀ p ∈ U ×ˢ sphere c R, F p ≠ 0) :
    ∃ d : ℕ, ∀ᶠ y in 𝓝 x, moment (fun z => F (y, z)) c R 0 = d := by
  have hnat : ∀ y ∈ U, ∃ d : ℕ, moment (fun z => F (y, z)) c R 0 = d := by
    intro y hy
    exact exists_nat_moment_zero hR (analyticOnNhd_slice hW hF y
      (fun z hz => hUW ⟨hy, hz⟩)) (fun z hz => hn (y, z) ⟨hy, hz⟩)
  obtain ⟨d, hd⟩ := hnat x hx
  refine ⟨d, ?_⟩
  have hcont := continuousAt_moment hW hF hU hx hR.le
    (fun p hp => hUW ⟨hp.1, sphere_subset_closedBall hp.2⟩) hn 0
  have heq := eventually_eq_of_continuousAt_nat_values hcont
    (by filter_upwards [hU.mem_nhds hx] with y hy; exact hnat y hy)
  simpa only [hd] using heq

/-- Compactness of the circle preserves the absence of boundary zeros on
an actual open neighborhood of the base parameter. -/
theorem exists_disk_family_neighborhood {n : ℕ} {F : (Fin n → ℂ) × ℂ → ℂ}
    {W : Set ((Fin n → ℂ) × ℂ)} (hW : IsOpen W) (hF : ContinuousOn F W)
    {x : Fin n → ℂ} {c : ℂ} {R : ℝ}
    (hbase : ∀ z ∈ closedBall c R, (x, z) ∈ W)
    (hn : ∀ z ∈ sphere c R, F (x, z) ≠ 0) :
    ∃ U : Set (Fin n → ℂ), IsOpen U ∧ x ∈ U ∧
      U ×ˢ closedBall c R ⊆ W ∧ ∀ p ∈ U ×ˢ sphere c R, F p ≠ 0 := by
  have hbase' : ({x} : Set (Fin n → ℂ)) ×ˢ closedBall c R ⊆ W := by
    rintro ⟨y, z⟩ ⟨hy, hz⟩
    rcases mem_singleton_iff.mp hy with rfl
    exact hbase z hz
  obtain ⟨U₁, V₁, hU₁, _, hx₁, hV₁, hUV₁⟩ := generalized_tube_lemma
    isCompact_singleton (isCompact_closedBall c R) hW hbase'
  have hopen : IsOpen (W ∩ F ⁻¹' ({0} : Set ℂ)ᶜ) :=
    hF.isOpen_inter_preimage hW isClosed_singleton.isOpen_compl
  have hsphere : ({x} : Set (Fin n → ℂ)) ×ˢ sphere c R ⊆
      W ∩ F ⁻¹' ({0} : Set ℂ)ᶜ := by
    rintro ⟨y, z⟩ ⟨hy, hz⟩
    rcases mem_singleton_iff.mp hy with rfl
    exact ⟨hbase z (sphere_subset_closedBall hz), hn z hz⟩
  obtain ⟨U₂, V₂, hU₂, _, hx₂, hV₂, hUV₂⟩ := generalized_tube_lemma
    isCompact_singleton (isCompact_sphere c R) hopen hsphere
  refine ⟨U₁ ∩ U₂, hU₁.inter hU₂, ⟨hx₁ (mem_singleton x), hx₂ (mem_singleton x)⟩,
    fun p hp => hUV₁ ⟨hp.1.1, hV₁ hp.2⟩, ?_⟩
  exact fun p hp => (hUV₂ ⟨hp.1.2, hV₂ hp.2⟩).2

theorem moment_of_factorization {f u : ℂ → ℂ} {c : ℂ} {R : ℝ} {d : ℕ}
    (roots : Fin d → ℂ) (hR : 0 < R) (hr : ∀ i, roots i ∈ ball c R)
    (hu : AnalyticOnNhd ℂ u (closedBall c R))
    (hun : ∀ z ∈ closedBall c R, u z ≠ 0)
    (hfu : ∀ z ∈ closedBall c R,
      f =ᶠ[𝓝 z] (fun w => RootMomentsNe.Constructions.RootMoments.rootProduct roots w * u w)) (k : ℕ) :
    moment f c R k = ∑ i, roots i ^ k := by
  have heq : (∮ z in C(c, R), z ^ k * logDeriv f z) =
      (2 * Real.pi * I) * ∑ i, roots i ^ k := by
    calc
      _ = ∮ z in C(c, R), z ^ k *
          logDeriv (fun w => RootMomentsNe.Constructions.RootMoments.rootProduct roots w * u w) z := by
        apply circleIntegral.integral_congr hR.le
        intro z hz
        dsimp only
        congr 1
        exact (logDeriv_congr_nhds (hfu z (sphere_subset_closedBall hz))).eq_of_nhds
      _ = _ := RootMomentsNe.Constructions.RootMoments.integral_rootProduct_mul_nonvanishing roots hR hr hu hun k
  rw [moment, heq, ← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul]

/-- Starting with just one fiber free of boundary zeros gives a fixed degree
and actual polynomial-times-unit factorizations for all nearby fibers. -/
theorem exists_fixed_degree_factorization {n : ℕ} {F : (Fin n → ℂ) × ℂ → ℂ}
    {W : Set ((Fin n → ℂ) × ℂ)} (hW : IsOpen W)
    (hF : DifferentiableOn ℂ F W) {x : Fin n → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hbase : ∀ z ∈ closedBall c R, (x, z) ∈ W)
    (hn : ∀ z ∈ sphere c R, F (x, z) ≠ 0) :
    ∃ (d : ℕ) (U : Set (Fin n → ℂ)), IsOpen U ∧ x ∈ U ∧
      U ×ˢ closedBall c R ⊆ W ∧ (∀ p ∈ U ×ˢ sphere c R, F p ≠ 0) ∧
      ∀ y ∈ U, ∃ (roots : Fin d → ℂ) (u : ℂ → ℂ),
        (∀ i, roots i ∈ ball c R) ∧ AnalyticOnNhd ℂ u (closedBall c R) ∧
        (∀ z ∈ closedBall c R, u z ≠ 0) ∧
        (∀ z ∈ closedBall c R, (fun w => F (y, w)) =ᶠ[𝓝 z]
          (fun w => RootMomentsNe.Constructions.RootMoments.rootProduct roots w * u w)) ∧
        ∀ k : ℕ, moment (fun z => F (y, z)) c R k = ∑ i, roots i ^ k := by
  obtain ⟨U, hU, hx, hUW, hUn⟩ :=
    exists_disk_family_neighborhood hW hF.continuousOn hbase hn
  obtain ⟨d, hd⟩ := locally_constant_root_count hW hF hU hx hR hUW hUn
  obtain ⟨V, hVd, hV, hxV⟩ := _root_.mem_nhds_iff.mp hd
  refine ⟨d, U ∩ V, hU.inter hV, ⟨hx, hxV⟩,
    fun p hp => hUW ⟨hp.1.1, hp.2⟩,
    fun p hp => hUn p ⟨hp.1.1, hp.2⟩, ?_⟩
  intro y hy
  have hya := analyticOnNhd_slice hW hF y (fun z hz => hUW ⟨hy.1, hz⟩)
  have hyn : ∀ z ∈ sphere c R, F (y, z) ≠ 0 := fun z hz => hUn (y, z) ⟨hy.1, hz⟩
  obtain ⟨e, roots, u, hr, hu, hun, hfu⟩ :=
    ClosedDiskFactorization.Constructions.DiskFactorization.exists_root_tuple_unit_on_closedDisk hya
      (exists_nonzero_in_ball hR hya.continuousOn hyn) hyn
  have hm := moment_of_factorization roots hR hr hu hun hfu
  have he : e = d := by
    apply Nat.cast_injective (R := ℂ)
    calc
      (e : ℂ) = moment (fun z => F (y, z)) c R 0 := by simpa using (hm 0).symm
      _ = d := hVd hy.2
  subst e
  exact ⟨roots, u, hr, hu, hun, hfu, hm⟩

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.RootFamiliesAt.Constructions.RootFamilies
