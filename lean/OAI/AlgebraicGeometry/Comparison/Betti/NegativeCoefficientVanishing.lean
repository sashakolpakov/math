import OAI.AlgebraicGeometry.Comparison.Betti.HomogeneousSectorSingle

/-! # Negative Coefficient Vanishing -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.NegativeCoefficientVanishing.Dolbeault

noncomputable section

section

/-! A full-negative homogeneous entire coefficient vanishes for nonnegative twist. -/

open _root_.TopologicalSpace

theorem continuous_inverse_homogeneous_zero {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (hf : Continuous f) (hf0 : f 0 = 0) (d : ℕ)
    (hscale : ∀ c : ℂ, c ≠ 0 → ∀ x, f (c⁻¹ • x) = c ^ d * f x) :
    ∀ x, f x = 0 := by
  intro x
  have hc : Continuous (fun c : ℂ => c ^ d * f (c • x)) :=
    (continuous_id.pow d).mul (hf.comp (continuous_id.smul continuous_const))
  have he : (fun c : ℂ => c ^ d * f (c • x)) = fun _ => f x := by
    apply Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hc continuous_const
    intro c hc0
    have hne : c ≠ 0 := hc0
    have hs := hscale c⁻¹ (inv_ne_zero hne) x
    rw [inv_inv, inv_pow] at hs
    change c ^ d * f (c • x) = f x
    rw [hs, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d hne), one_mul]
  have hz := congrFun he 0
  simpa only [zero_smul, hf0, mul_zero] using hz.symm

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem fullNegativeCoefficient_zero_nonneg (d : ℤ) (hd : 0 ≤ d)
    (a : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (Finset.univ : Finset ι) d) : a = 0 := by
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hd
  have ha0 : Laurent.SectorSum.Dolbeault.laurentEntireFunction a.val (0 : ι → ℂ) = 0 := by
    let i : ι := Classical.choice inferInstance
    exact a.property.1 i (Finset.mem_univ i) ⟨0, trivial⟩ rfl
  have hscale : ∀ c : ℂ, c ≠ 0 → ∀ x : ι → ℂ,
      Laurent.SectorSum.Dolbeault.laurentEntireFunction a.val (c⁻¹ • x) = c ^ k * Laurent.SectorSum.Dolbeault.laurentEntireFunction a.val x := by
    intro c hc x
    have hpoint : Laurent.FiniteUniqueness.Dolbeault.laurentSectorScale c (Finset.univ : Finset ι) x = c⁻¹ • x := by
      funext i
      simp only [Laurent.FiniteUniqueness.Dolbeault.laurentSectorScale, Finset.mem_univ, ite_true, Pi.smul_apply, smul_eq_mul]
    exact (congrArg (Laurent.SectorSum.Dolbeault.laurentEntireFunction a.val) hpoint).symm.trans
      ((a.property.2 c hc x).trans (by rw [zpow_natCast]))
  have hzero := continuous_inverse_homogeneous_zero (Laurent.SectorSum.Dolbeault.laurentEntireFunction a.val)
    (Laurent.SectorSum.Dolbeault.laurentEntireFunction_differentiable a.val).continuous ha0 k hscale
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact hzero x.val

end

/-! All-positive entire Laurent coefficients of negative degree vanish. -/

theorem continuous_inverse_homogeneous_zero_of_pos {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (hf : Continuous f) (d : ℕ) (hd : 0 < d)
    (hscale : ∀ c : ℂ, c ≠ 0 → ∀ x, f (c⁻¹ • x) = c ^ d * f x) :
    ∀ x, f x = 0 := by
  intro x
  have hc : Continuous (fun c : ℂ => c ^ d * f (c • x)) :=
    (continuous_id.pow d).mul (hf.comp (continuous_id.smul continuous_const))
  have he : (fun c : ℂ => c ^ d * f (c • x)) = fun _ => f x := by
    apply Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hc continuous_const
    intro c hc0
    have hne : c ≠ 0 := hc0
    have hs := hscale c⁻¹ (inv_ne_zero hne) x
    rw [inv_inv, inv_pow] at hs
    change c ^ d * f (c • x) = f x
    rw [hs, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero d hne), one_mul]
  have hz := congrFun he 0
  simpa only [zero_pow (Nat.ne_of_gt hd), zero_mul] using hz.symm

theorem positiveCoefficient_zero_neg {ι : Type} [Fintype ι] [DecidableEq ι]
    (d : ℤ) (hd : d < 0) (a : HomogeneousSectorSingle.Dolbeault.homogeneousSectorCoefficients (∅ : Finset ι) d) : a = 0 := by
  have hk : 0 < (-d).toNat := by omega
  have hscale : ∀ c : ℂ, c ≠ 0 → ∀ x : ι → ℂ,
      Laurent.SectorSum.Dolbeault.laurentEntireFunction a.val (c⁻¹ • x) = c ^ (-d).toNat * Laurent.SectorSum.Dolbeault.laurentEntireFunction a.val x := by
    intro c hc x
    have hpoint : Laurent.FiniteUniqueness.Dolbeault.laurentSectorScale c⁻¹ (∅ : Finset ι) x = c⁻¹ • x := by
      funext i
      simp only [Laurent.FiniteUniqueness.Dolbeault.laurentSectorScale, Finset.notMem_empty, ite_false, Pi.smul_apply, smul_eq_mul]
    have hpower : (c⁻¹) ^ d = c ^ (-d).toNat := by
      rw [inv_zpow, ← zpow_neg, ← Int.toNat_of_nonneg (neg_nonneg.mpr hd.le), zpow_natCast]
      rfl
    exact (congrArg (Laurent.SectorSum.Dolbeault.laurentEntireFunction a.val) hpoint).symm.trans
      ((a.property.2 c⁻¹ (inv_ne_zero hc) x).trans
        (congrArg (· * Laurent.SectorSum.Dolbeault.laurentEntireFunction a.val x) hpower))
  have hzero := continuous_inverse_homogeneous_zero_of_pos (Laurent.SectorSum.Dolbeault.laurentEntireFunction a.val)
    (Laurent.SectorSum.Dolbeault.laurentEntireFunction_differentiable a.val).continuous (-d).toNat hk hscale
  apply Subtype.ext
  apply Subtype.ext
  funext x
  exact hzero x.val

end

end OAI.AlgebraicGeometry.Comparison.Betti.NegativeCoefficientVanishing.Dolbeault
