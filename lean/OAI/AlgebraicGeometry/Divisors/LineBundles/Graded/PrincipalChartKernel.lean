import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.HomogeneousDivision
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.ChartMultiplication
import OAI.AlgebraicGeometry.Divisors.LineBundles.Projective.MapBase

/-! # Principal Chart Kernel -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.PrincipalChartKernel.BundleCycles

noncomputable section

/-! The actual chart map of a homogeneous principal quotient has the
expected principal kernel in every degree-one chart. -/

open _root_.HomogeneousLocalization

variable {A B σ τ : Type*} [CommRing A] [CommRing B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) {t s : A} (ht : t ∈ 𝒜 1) (hs : s ∈ 𝒜 1)
    (hker : RingHom.ker f.toRingHom = Ideal.span {t})

include hker in
theorem gradedPrincipalChart_kernel :
    RingHom.ker (Away.map f s) =
      Ideal.span {Away.mk 𝒜 hs 1 t (by simpa only [one_smul] using ht)} := by
  have ht0 : f t = 0 := by
    have hm : t ∈ RingHom.ker f.toRingHom := hker.symm ▸ Ideal.subset_span (Set.mem_singleton t)
    exact hm
  apply le_antisymm
  · intro z hz
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hs z
    have hv := congrArg HomogeneousLocalization.val hz
    rw [Away.map_mk, Away.val_mk, val_zero, Localization.mk_eq_mk'] at hv
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.mk'_eq_zero_iff (f a)
      (⟨f s ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (f s))).mp hv
    have hdiv : t ∣ a * s ^ (k + 1) := by
      apply Ideal.mem_span_singleton.mp
      rw [← hker]
      change f (a * s ^ (k + 1)) = 0
      rw [map_mul, map_pow, pow_succ]
      have h : f a * (f s ^ k * f s) = (f s ^ k * f a) * f s := by ring
      rw [h, hk, zero_mul]
    have hdegree : a * s ^ (k + 1) ∈ 𝒜 (1 + (n + k)) := by
      have ha' : a ∈ 𝒜 n := by simpa only [smul_eq_mul, mul_one] using ha
      have hs' : s ^ (k + 1) ∈ 𝒜 (k + 1) := by
        simpa only [smul_eq_mul, mul_one] using SetLike.pow_mem_graded (k + 1) hs
      have hi : 1 + (n + k) = n + (k + 1) := by omega
      rw [hi]
      exact SetLike.mul_mem_graded ha' hs'
    obtain ⟨b, hb, hab⟩ := HomogeneousDivision.BundleCycles.graded_homogeneous_division 𝒜 ht hdegree hdiv
    apply Ideal.mem_span_singleton.mpr
    refine ⟨Away.mk 𝒜 hs (n + k) b (by simpa only [smul_eq_mul, mul_one] using hb), ?_⟩
    symm
    apply HomogeneousLocalization.val_injective
    rw [val_mul, Away.val_mk, Away.val_mk, Away.val_mk, Localization.mk_mul,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul]
    rw [← hab]
    simp only [pow_add, pow_one]
    ring
  · apply Ideal.span_le.mpr
    intro z hz
    obtain rfl : z = Away.mk 𝒜 hs 1 t (by simpa only [one_smul] using ht) := hz
    change Away.map f s (Away.mk 𝒜 hs 1 t _) = 0
    apply HomogeneousLocalization.val_injective
    rw [Away.map_mk, Away.val_mk, val_zero, ht0]
    exact Localization.mk_zero _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.PrincipalChartKernel.BundleCycles
