import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Cartan
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel

/-! # Rational Span -/

namespace OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalSpan

noncomputable section

/-! Every spherical operator is a finite rational linear combination of
the constructed raw double-coset operators. -/

open scoped Classical

section General

variable {G I : Type*} [Group G] (U : Subgroup G)

theorem kernel_sub_smul_raw_apply (S T : HeckeKernel.SphericalHecke U) {g : G}
    (hT : HeckeKernel.IsRawDoubleCoset U g T) {x : G ⧸ U} (hx : x ∈ HeckeKernel.doubleCosetOrbit U g)
    (r : ℚ) (hr : HeckeKernel.kernel U S x = r) (y : G ⧸ U) :
    HeckeKernel.kernel U (S - r • T) y =
      if y ∈ HeckeKernel.doubleCosetOrbit U g then 0 else HeckeKernel.kernel U S y := by
  have hlin : HeckeKernel.kernel U (S - r • T) = HeckeKernel.kernel U S - r • HeckeKernel.kernel U T := by
    exact (HeckeKernel.kernelLinear U).map_sub S (r • T) |>.trans
      (congrArg (fun z => HeckeKernel.kernel U S - z) ((HeckeKernel.kernelLinear U).map_smul r T))
  rw [hlin]
  change HeckeKernel.kernel U S y - r * HeckeKernel.kernel U T y = _
  rw [HeckeKernel.raw_kernel_at U hT]
  by_cases hy : y ∈ HeckeKernel.doubleCosetOrbit U g
  · rw [ite_eq_left hy, ite_eq_left hy, HeckeKernel.kernel_eq_of_same_orbit U S g hy hx, hr, mul_one, sub_self]
  · rw [ite_eq_right hy, ite_eq_right hy, mul_zero, sub_zero]

theorem exists_raw_rational_expansion (rep : I → G) (basis : I → HeckeKernel.SphericalHecke U)
    (hraw : ∀ i, HeckeKernel.IsRawDoubleCoset U (rep i) (basis i))
    (hcover : ∀ x : G ⧸ U, ∃ i, x ∈ HeckeKernel.doubleCosetOrbit U (rep i)) (T : HeckeKernel.SphericalHecke U) :
    ∃ c : I →₀ ℚ, T = Finsupp.linearCombination ℚ basis c := by
  suffices ∀ (s : Finset (G ⧸ U)) (S : HeckeKernel.SphericalHecke U),
      (HeckeKernel.kernel U S).support = s → ∃ c : I →₀ ℚ, S = Finsupp.linearCombination ℚ basis c by
    exact this _ T rfl
  intro s
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    intro S hs
    by_cases hempty : s = ∅
    · refine ⟨0, ?_⟩
      rw [map_zero]
      apply HeckeKernel.kernel_injective U
      exact Finsupp.support_eq_empty.mp (hs.trans hempty)
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨i, hi⟩ := hcover x
    let r := HeckeKernel.kernel U S x
    let R := S - r • basis i
    have hval (y : G ⧸ U) : HeckeKernel.kernel U R y =
        if y ∈ HeckeKernel.doubleCosetOrbit U (rep i) then 0 else HeckeKernel.kernel U S y :=
      kernel_sub_smul_raw_apply U S (basis i) (hraw i) hi r rfl y
    have hsub : (HeckeKernel.kernel U R).support ⊆ s := by
      intro y hy
      rw [Finsupp.mem_support_iff, hval] at hy
      by_cases hmem : y ∈ HeckeKernel.doubleCosetOrbit U (rep i)
      · rw [ite_eq_left hmem] at hy
        exact False.elim (hy rfl)
      · rw [ite_eq_right hmem] at hy
        rw [← hs]
        exact Finsupp.mem_support_iff.mpr hy
    have hnot : x ∉ (HeckeKernel.kernel U R).support := by
      rw [Finsupp.mem_support_iff, hval, ite_eq_left hi]
      exact not_not_intro rfl
    have hstrict : (HeckeKernel.kernel U R).support ⊂ s :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hnot (heq.symm ▸ hx)⟩
    obtain ⟨c, hc⟩ := ih _ hstrict R rfl
    refine ⟨c + Finsupp.single i r, ?_⟩
    rw [map_add, Finsupp.linearCombination_single]
    change S - r • basis i = _ at hc
    exact (sub_eq_iff_eq_add (a := S) (b := r • basis i)).mp hc

end General

variable (s q : ℕ) [Fact q.Prime]

theorem exists_spherical_rational_expansion (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (T : HeckeKernel.Hecke s q) :
    ∃ c : Local.LocalType s →₀ ℚ, T = c.sum (fun t r => r • CentralConvolution.sphericalBasis s q t) := by
  apply exists_raw_rational_expansion (HeckeKernel.integralLevel s q) (HeckeKernel.representative s q)
    (CentralConvolution.sphericalBasis s q) (CentralConvolution.sphericalBasis_isRaw s q)
  intro x
  induction x using Quotient.inductionOn with
  | h x =>
    obtain ⟨t, l, r, hxr⟩ := Cartan.exists_split_cartan q s hElementaryDivisors x⁻¹
    refine ⟨t, (HeckeKernel.mem_doubleCosetOrbit _ _ _).mpr ⟨r⁻¹, l⁻¹, ?_⟩⟩
    have h := congrArg Inv.inv hxr
    simpa only [inv_inv, mul_inv_rev, Subgroup.coe_inv, mul_assoc] using h

theorem sphericalBasis_span (hElementaryDivisors : Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) :
    Submodule.span ℚ (Set.range (CentralConvolution.sphericalBasis s q)) = ⊤ := by
  rw [← Finsupp.range_linearCombination]
  apply LinearMap.range_eq_top.mpr
  intro T
  obtain ⟨c, hc⟩ := exists_spherical_rational_expansion s q hElementaryDivisors T
  exact ⟨c, hc.symm⟩

end

end OAI.AlgebraicGeometry.AbelianScheme.TateComparison.RationalSpan
