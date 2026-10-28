import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel

/-! # Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Coefficients.Construction

noncomputable section

/-! Positivity determines the coefficients when a raw expansion is
supported on a single distinguished double coset. -/

open scoped Classical

open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel

variable {G I : Type*} [Group G] (U : Subgroup G)

theorem raw_expansion_single (rep : I → G) (basis : I → TateComparison.HeckeKernel.SphericalHecke U)
    (hraw : ∀ i, TateComparison.HeckeKernel.IsRawDoubleCoset U (rep i) (basis i)) (w : I)
    (hunique : ∀ i, (QuotientGroup.mk (rep i)⁻¹ : G ⧸ U) ∈ TateComparison.HeckeKernel.doubleCosetOrbit U (rep w) → i = w)
    (c : I →₀ ℕ) (hc : basis w = c.sum (fun i n => n • basis i)) :
    c = Finsupp.single w 1 := by
  have hself (i : I) : TateComparison.HeckeKernel.kernel U (basis i) (QuotientGroup.mk (rep i)⁻¹) = 1 := by
    rw [hraw i, ite_eq_left]
    exact ⟨1, 1, by simp⟩
  have hsupport : ∀ i ∈ c.support, i = w := by
    intro i hi
    let x : G ⧸ U := QuotientGroup.mk (rep i)⁻¹
    let ev : TateComparison.HeckeKernel.SphericalHecke U →ₗ[ℚ] ℚ := {
      toFun := fun T => TateComparison.HeckeKernel.kernel U T x
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
    have he := congrArg ev hc
    simp only [Finsupp.sum, map_sum, nsmul_eq_mul] at he
    have hnonneg (j : I) : 0 ≤ ev (basis j) := by
      obtain ⟨m, hm⟩ := TateComparison.HeckeKernel.raw_natValued U (hraw j) x
      change 0 ≤ TateComparison.HeckeKernel.kernel U (basis j) x
      rw [hm]
      positivity
    have hle : (c i : ℚ) ≤ ∑ j ∈ c.support, (c j : ℚ) * ev (basis j) := by
      have hb := Finset.single_le_sum
        (f := fun j => (c j : ℚ) * ev (basis j))
        (fun j _ => mul_nonneg (Nat.cast_nonneg _) (hnonneg j)) hi
      have hei : ev (basis i) = 1 := hself i
      simpa only [hei, mul_one] using hb
    have hpos : 0 < ev (basis w) := by
      rw [he]
      exact lt_of_lt_of_le (by exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)) hle
    apply hunique i
    by_contra hnot
    change 0 < TateComparison.HeckeKernel.kernel U (basis w) x at hpos
    rw [TateComparison.HeckeKernel.raw_kernel_at U (hraw w), ite_eq_right hnot] at hpos
    exact (lt_irrefl 0) hpos
  have heq : c = Finsupp.single w (c w) := by
    ext i
    by_cases hi : i = w
    · subst i
      simp
    · have hz : c i = 0 := Finsupp.notMem_support_iff.mp (fun hm => hi (hsupport i hm))
      simp [hi, hz]
  have hcw : c w = 1 := by
    have he := congrArg (fun T => TateComparison.HeckeKernel.kernel U T (QuotientGroup.mk (rep w)⁻¹)) hc
    rw [heq, Finsupp.sum_single_index] at he
    · change TateComparison.HeckeKernel.kernel U (basis w) (QuotientGroup.mk (rep w)⁻¹) =
        (c w : ℕ) • TateComparison.HeckeKernel.kernel U (basis w) (QuotientGroup.mk (rep w)⁻¹) at he
      rw [hself, nsmul_eq_mul, mul_one] at he
      exact_mod_cast he.symm
    · simp
  rw [heq, hcw]

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.Coefficients.Construction
