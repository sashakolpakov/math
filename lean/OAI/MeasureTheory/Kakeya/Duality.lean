import OAI.MeasureTheory.Kakeya.Overlap

open _root_.MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- Independent choices commute with a finite sum of nonnegative extended
reals. It permits taking the supremum over the center of each tube after a
uniform estimate for every choice of centers has been proved. -/
theorem finsetSum_iSup_independent {m : ℕ} {β : Type*} [Nonempty β]
    (F : Fin m → β → ℝ≥0∞) :
    (∑ i, ⨆ b, F i b) = ⨆ b : Fin m → β, ∑ i, F i (b i) := by
  classical
  have heval (i : Fin m) : (⨆ b : Fin m → β, F i (b i)) = ⨆ b, F i b := by
    apply le_antisymm
    · exact iSup_le fun b ↦ le_iSup (F i) (b i)
    · exact iSup_le fun b ↦ le_iSup (fun b' : Fin m → β ↦ F i (b' i)) (fun _ ↦ b)
  simp_rw [← heval]
  apply ENNReal.finsetSum_iSup
  intro u v
  refine ⟨fun i ↦ if F i (u i) ≤ F i (v i) then v i else u i, ?_⟩
  intro i
  dsimp only
  split_ifs with h
  · exact ⟨h, le_rfl⟩
  · exact ⟨le_rfl, le_of_not_ge h⟩

/-- Finite-dimensional positive `ℓp` duality, proved by the optimizing vector
`aᵢ = yᵢ^(p-1)` rather than by assuming a duality theorem. -/
theorem finite_lp_duality_nonneg {m : ℕ} {p q B : ℝ} (hpq : p.HolderConjugate q)
    (y : Fin m → ℝ) (hy : ∀ i, 0 ≤ y i) (hB : 0 ≤ B)
    (hdual : ∀ a : Fin m → ℝ, (∀ i, 0 ≤ a i) →
      (∑ i, a i * y i) ≤ B * (∑ i, a i ^ q) ^ (1 / q)) :
    (∑ i, y i ^ p) ^ (1 / p) ≤ B := by
  let S : ℝ := ∑ i, y i ^ p
  have hS : 0 ≤ S := Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (hy i) p
  by_cases hzero : S = 0
  · change S ^ (1 / p) ≤ B
    rw [hzero, Real.zero_rpow hpq.one_div_ne_zero]
    exact hB
  have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
  have hopt (i : Fin m) : y i ^ (p - 1) * y i = y i ^ p := by
    by_cases hi : y i = 0
    · simp [hi, Real.zero_rpow hpq.sub_one_ne_zero, Real.zero_rpow hpq.ne_zero]
    · calc
        y i ^ (p - 1) * y i = y i ^ (p - 1) * y i ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = y i ^ ((p - 1) + 1) := (Real.rpow_add (lt_of_le_of_ne (hy i) (Ne.symm hi)) _ _).symm
        _ = y i ^ p := by congr 1; ring
  have hnorm (i : Fin m) : (y i ^ (p - 1)) ^ q = y i ^ p := by
    rw [← Real.rpow_mul (hy i), hpq.sub_one_mul_conj]
  have h := hdual (fun i ↦ y i ^ (p - 1)) (fun i ↦ Real.rpow_nonneg (hy i) _)
  simp only [hopt, hnorm] at h
  change S ≤ B * S ^ (1 / q) at h
  have hd : S / S ^ (1 / q) ≤ B := (div_le_iff₀ (Real.rpow_pos_of_pos hSpos _)).mpr h
  have he : 1 - 1 / q = 1 / p := by simpa only [one_div] using hpq.symm.one_sub_inv
  have hquot : S / S ^ (1 / q) = S ^ (1 / p) := by
    conv_lhs => lhs; rw [← Real.rpow_one S]
    rw [← Real.rpow_sub hSpos, he]
  rw [hquot] at hd
  exact hd

/-- Duality turns a weighted set-overlap estimate into an estimate for the
vector of integrals over the sets. This applies to tube families, without
requiring the ambient `Lp` function to be globally integrable. -/
theorem finite_set_integrals_of_overlap
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {m : ℕ}
    {p q B : ℝ} (hpq : p.HolderConjugate q) (hB : 0 ≤ B)
    (T : Fin m → Set α) (hT : ∀ i, MeasurableSet (T i))
    (hTfin : ∀ i, μ (T i) < ∞)
    (hoverlap : ∀ a : Fin m → ℝ, (∀ i, 0 ≤ a i) →
      MemLp (fun x ↦ ∑ i, (T i).indicator (fun _ ↦ a i) x) (ENNReal.ofReal q) μ ∧
      (∫ x, (∑ i, (T i).indicator (fun _ ↦ a i) x) ^ q ∂μ) ^ (1 / q) ≤
        B * (∑ i, a i ^ q) ^ (1 / q))
    {f : α → ℂ} (hf : MemLp f (ENNReal.ofReal p) μ) :
    (∑ i, (∫ x in T i, ‖f x‖ ∂μ) ^ p) ^ (1 / p) ≤
      B * (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p) := by
  have hi (i : Fin m) : IntegrableOn (fun x ↦ ‖f x‖) (T i) μ := by
    have : IsFiniteMeasure (μ.restrict (T i)) := ⟨by simpa using hTfin i⟩
    exact (hf.norm.mono_measure Measure.restrict_le_self).integrable
      (ENNReal.one_le_ofReal.mpr hpq.lt.le)
  apply finite_lp_duality_nonneg hpq
    (fun i ↦ ∫ x in T i, ‖f x‖ ∂μ)
    (fun i ↦ integral_nonneg fun x ↦ norm_nonneg (f x))
    (mul_nonneg hB (Real.rpow_nonneg (integral_nonneg fun x ↦
      Real.rpow_nonneg (norm_nonneg (f x)) _) _))
  intro a ha
  let φ : α → ℝ := fun x ↦ ∑ i, (T i).indicator (fun _ ↦ a i) x
  obtain ⟨hφ, hφbound⟩ := hoverlap a ha
  have hφnonneg (x : α) : 0 ≤ φ x := by
    exact Finset.sum_nonneg fun i _ ↦ Set.indicator_nonneg (fun _ _ ↦ ha i) x
  have hind (i : Fin m) : Integrable ((T i).indicator (fun x ↦ a i * ‖f x‖)) μ :=
    (integrable_indicator_iff (hT i)).mpr ((hi i).const_mul (a i))
  have heq : (fun x ↦ ‖f x‖ * φ x) =
      fun x ↦ ∑ i, (T i).indicator (fun x ↦ a i * ‖f x‖) x := by
    funext x
    simp only [φ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hx : x ∈ T i <;> simp [hx, mul_comm]
  have hpair : (∫ x, ‖f x‖ * φ x ∂μ) = ∑ i, a i * ∫ x in T i, ‖f x‖ ∂μ := by
    rw [heq, integral_finsetSum Finset.univ (fun i _ ↦ hind i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_indicator (hT i), integral_const_mul]
  rw [← hpair]
  calc
    (∫ x, ‖f x‖ * φ x ∂μ) ≤
        (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p) * (∫ x, φ x ^ q ∂μ) ^ (1 / q) :=
      integral_mul_le_Lp_mul_Lq_of_nonneg hpq
        (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
        (Filter.Eventually.of_forall hφnonneg) hf.norm hφ
    _ ≤ (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p) * (B * (∑ i, a i ^ q) ^ (1 / q)) :=
      mul_le_mul_of_nonneg_left hφbound (Real.rpow_nonneg
        (integral_nonneg fun x ↦ Real.rpow_nonneg (norm_nonneg (f x)) _) _)
    _ = _ := by ring

end OAI.MeasureTheory.Kakeya
