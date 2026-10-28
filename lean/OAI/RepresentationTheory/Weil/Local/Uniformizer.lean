import OAI.RepresentationTheory.Weil.Local.PrincipalSquareClasses

/-! # Uniformizer -/

namespace OAI.RepresentationTheory.Weil.Local.Uniformizer.Construction

noncomputable section

section

/-! A uniformizer and discrete norm values, obtained directly from compact ultrametric balls. -/

open Set _root_.Metric

theorem exists_local_uniformizer
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k]
    (hnd : ¬ DiscreteTopology k) :
    ∃ π : kˣ, ‖π.val‖ < 1 ∧ ∀ x : k, ‖x‖ < 1 → ‖x‖ ≤ ‖π.val‖ := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField k with hd | ⟨_, rfl⟩
  · exact (hnd hd).elim
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hnd
  have hc : IsCompact (Metric.ball (0 : k) 1) :=
    (isCompact_closedBall (0 : k) 1).of_isClosed_subset
      (IsUltrametricDist.isClosed_ball 0 1) Metric.ball_subset_closedBall
  obtain ⟨x, hx, hmax⟩ := hc.exists_isMaxOn ⟨0, by simp⟩ continuous_norm.continuousOn
  obtain ⟨y, hy0, hy1⟩ := NormedField.exists_norm_lt_one k
  have hxy : ‖y‖ ≤ ‖x‖ := hmax (by simpa only [Metric.mem_ball, dist_zero_right] using hy1)
  have hx0 : x ≠ 0 := norm_pos_iff.mp (hy0.trans_le hxy)
  refine ⟨Units.mk0 x hx0, ?_, fun z hz => hmax ?_⟩
  · change ‖x‖ < 1
    simpa only [Metric.mem_ball, dist_zero_right] using hx
  · simpa only [Metric.mem_ball, dist_zero_right] using hz

theorem norm_eq_uniformizer_pow_of_le_one
    {k : Type*} [NormedField k] (π : kˣ) (hπ : ‖π.val‖ < 1)
    (hmax : ∀ x : k, ‖x‖ < 1 → ‖x‖ ≤ ‖π.val‖)
    (x : k) (hx0 : x ≠ 0) (hx1 : ‖x‖ ≤ 1) :
    ∃ n : ℕ, ‖x‖ = ‖π.val‖ ^ n := by
  have hπ0 : 0 < ‖π.val‖ := norm_pos_iff.mpr π.ne_zero
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one (norm_pos_iff.mpr hx0) hx1 hπ0 hπ
  have hp0 : 0 < ‖π.val‖ ^ n := pow_pos hπ0 n
  have hy : ‖x / π.val ^ n‖ = ‖x‖ / ‖π.val‖ ^ n := by rw [norm_div, norm_pow]
  have hyle : ‖x / π.val ^ n‖ ≤ 1 := by rw [hy, div_le_one hp0]; exact hn'
  have hygt : ‖π.val‖ < ‖x / π.val ^ n‖ := by
    rw [hy, lt_div_iff₀ hp0]
    simpa only [pow_succ, mul_comm] using hn
  have hyeq : ‖x / π.val ^ n‖ = 1 := by
    apply le_antisymm hyle
    by_contra! hh
    exact (not_lt_of_ge (hmax _ hh)) hygt
  refine ⟨n, ?_⟩
  rw [hy, div_eq_one_iff_eq (ne_of_gt hp0)] at hyeq
  exact hyeq

theorem norm_eq_uniformizer_zpow
    {k : Type*} [NormedField k] (π : kˣ) (hπ : ‖π.val‖ < 1)
    (hmax : ∀ x : k, ‖x‖ < 1 → ‖x‖ ≤ ‖π.val‖) (x : kˣ) :
    ∃ n : ℤ, ‖x.val‖ = ‖π.val‖ ^ n := by
  by_cases hx1 : ‖x.val‖ ≤ 1
  · obtain ⟨n, hn⟩ := norm_eq_uniformizer_pow_of_le_one π hπ hmax x.val x.ne_zero hx1
    exact ⟨n, by simpa only [zpow_natCast] using hn⟩
  · have hxinv : ‖x.val⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact (inv_le_one₀ (norm_pos_iff.mpr x.ne_zero)).mpr (le_of_not_ge hx1)
    obtain ⟨n, hn⟩ := norm_eq_uniformizer_pow_of_le_one π hπ hmax x.val⁻¹ (inv_ne_zero x.ne_zero) hxinv
    refine ⟨-(n : ℤ), ?_⟩
    rw [norm_inv] at hn
    simpa only [inv_inv, zpow_neg, zpow_natCast] using congrArg (fun t : ℝ => t⁻¹) hn

end

/-! Splitting the local field's multiplicative group into norm-one units and uniformizer powers. -/

variable {k : Type*} [NormedField k]

def uniformizerUnitsHom (π : kˣ) : PrincipalSquareClasses.Construction.normUnitSubgroup k × Multiplicative ℤ →* kˣ where
  toFun p := p.1.val * π ^ Multiplicative.toAdd p.2
  map_one' := by simp
  map_mul' p q := by
    change (p.1.val * q.1.val) * π ^ (Multiplicative.toAdd p.2 + Multiplicative.toAdd q.2) = _
    rw [zpow_add]
    change _ = (p.1.val * π ^ Multiplicative.toAdd p.2) * (q.1.val * π ^ Multiplicative.toAdd q.2)
    ac_rfl

theorem uniformizerUnitsHom_norm (π : kˣ) (p : PrincipalSquareClasses.Construction.normUnitSubgroup k × Multiplicative ℤ) :
    ‖(uniformizerUnitsHom π p).val‖ = ‖π.val‖ ^ Multiplicative.toAdd p.2 := by
  change ‖p.1.val.val * (π ^ Multiplicative.toAdd p.2).val‖ = _
  rw [norm_mul, Units.val_zpow_eq_zpow_val, norm_zpow,
    show ‖p.1.val.val‖ = 1 from p.1.property, one_mul]

theorem uniformizerUnitsHom_injective (π : kˣ) (hπ : ‖π.val‖ < 1) :
    Function.Injective (uniformizerUnitsHom π) := by
  intro p q he
  have hn := congrArg (fun x : kˣ => ‖x.val‖) he
  rw [uniformizerUnitsHom_norm, uniformizerUnitsHom_norm] at hn
  have hm : Multiplicative.toAdd p.2 = Multiplicative.toAdd q.2 :=
    (zpow_right_inj₀ (norm_pos_iff.mpr π.ne_zero) hπ.ne).mp hn
  apply Prod.ext
  · apply Subtype.ext
    change p.1.val * π ^ Multiplicative.toAdd p.2 = q.1.val * π ^ Multiplicative.toAdd q.2 at he
    rw [hm] at he
    exact mul_right_cancel he
  · exact congrArg Multiplicative.ofAdd hm

theorem uniformizerUnitsHom_surjective (π : kˣ) (hπ : ‖π.val‖ < 1)
    (hmax : ∀ x : k, ‖x‖ < 1 → ‖x‖ ≤ ‖π.val‖) :
    Function.Surjective (uniformizerUnitsHom π) := by
  intro x
  obtain ⟨n, hn⟩ := norm_eq_uniformizer_zpow π hπ hmax x
  let u : PrincipalSquareClasses.Construction.normUnitSubgroup k := ⟨x / π ^ n, by
    change ‖(x / π ^ n).val‖ = 1
    rw [Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val, norm_div, norm_zpow, hn]
    exact div_self (zpow_ne_zero n (norm_ne_zero_iff.mpr π.ne_zero))⟩
  refine ⟨(u, Multiplicative.ofAdd n), ?_⟩
  change (x / π ^ n) * π ^ n = x
  exact div_mul_cancel x (π ^ n)

def uniformizerUnitsEquiv (π : kˣ) (hπ : ‖π.val‖ < 1)
    (hmax : ∀ x : k, ‖x‖ < 1 → ‖x‖ ≤ ‖π.val‖) :
    PrincipalSquareClasses.Construction.normUnitSubgroup k × Multiplicative ℤ ≃* kˣ :=
  MulEquiv.ofBijective (uniformizerUnitsHom π)
    ⟨uniformizerUnitsHom_injective π hπ, uniformizerUnitsHom_surjective π hπ hmax⟩

theorem exists_localUnits_decomposition
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k]
    (hnd : ¬ DiscreteTopology k) : Nonempty (kˣ ≃* PrincipalSquareClasses.Construction.normUnitSubgroup k × Multiplicative ℤ) := by
  obtain ⟨π, hπ, hmax⟩ := exists_local_uniformizer hnd
  exact ⟨(uniformizerUnitsEquiv π hπ hmax).symm⟩

end

end OAI.RepresentationTheory.Weil.Local.Uniformizer.Construction
