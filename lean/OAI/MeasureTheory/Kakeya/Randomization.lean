import OAI.MeasureTheory.Kakeya.Packets

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped BigOperators

noncomputable section
namespace OAI.MeasureTheory.Kakeya

/-- The independent sign space is finite, so no probability-space completion
or measurability assumptions are hidden in the randomization argument. -/
def splitSigns (n : ℕ) : (Fin (n + 1) → Bool) ≃ Bool × (Fin n → Bool) where
  toFun ε := (ε 0, fun i ↦ ε i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv ε := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
  right_inv p := by ext <;> simp

theorem sum_signs_succ {β : Type*} [AddCommMonoid β] (n : ℕ)
    (F : (Fin (n + 1) → Bool) → β) :
    ∑ ε, F ε = ∑ b : Bool, ∑ ε : Fin n → Bool, F (Fin.cons b ε) := by
  have h := (splitSigns n).symm.sum_comp F
  simpa only [Fintype.sum_prod_type, splitSigns, Equiv.coe_fn_symm_mk] using h.symm

def signedSum {m : ℕ} (z : Fin m → ℂ) (ε : Fin m → Bool) : ℂ :=
  ∑ i, if ε i then z i else -z i

theorem signedSum_cons {m : ℕ} (z : Fin (m + 1) → ℂ) (b : Bool) (ε : Fin m → Bool) :
    signedSum z (Fin.cons b ε) = (if b then z 0 else -z 0) + signedSum (fun i ↦ z i.succ) ε := by
  simp [signedSum, Fin.sum_univ_succ]

/-- For disjointly supported inputs, signs do not change the input `Lp`
power; this is the other half of the randomization argument. -/
theorem norm_signedSum_rpow_disjoint {m : ℕ} (z : Fin m → ℂ) (ε : Fin m → Bool)
    {p : ℝ} (hp : 0 < p) (hdis : ∀ i j, i ≠ j → z i = 0 ∨ z j = 0) :
    ‖signedSum z ε‖ ^ p = ∑ i, ‖z i‖ ^ p := by
  classical
  by_cases hz : ∀ i, z i = 0
  · simp [signedSum, hz, Real.zero_rpow hp.ne']
  · obtain ⟨i, hi⟩ := not_forall.mp hz
    have hzero (j : Fin m) (hji : j ≠ i) : z j = 0 :=
      (hdis j i hji).resolve_right hi
    have hs : signedSum z ε = if ε i then z i else -z i := by
      unfold signedSum
      apply Finset.sum_eq_single i
      · intro j _ hji
        simp [hzero j hji]
      · simp
    have hr : (∑ j, ‖z j‖ ^ p) = ‖z i‖ ^ p := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        simp [hzero j hji, Real.zero_rpow hp.ne']
      · simp
    rw [hs, hr]
    cases ε i <;> simp

theorem norm_signedPackets_rpow {n m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (v x : Fin m → Space n) (c : Fin m → ℂ) (ε : Fin m → Bool)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (v i) (v j))
    {p : ℝ} (hp : 0 < p) (ω : Space n) :
    ‖signedSum (fun i ↦ c i * capPacket δ (v i) (x i) ω) ε‖ ^ p =
      ∑ i, ‖c i * capPacket δ (v i) (x i) ω‖ ^ p := by
  apply norm_signedSum_rpow_disjoint _ _ hp
  intro i j hij
  by_cases hωi : ω ∈ packetCap δ (v i)
  · right
    have hωj : ω ∉ packetCap δ (v j) := fun hj ↦
      Set.disjoint_left.mp (packetCaps_disjoint hδ (hsep i j hij)) hωi hj
    simp [capPacket, hωj]
  · left
    simp [capPacket, hωi]

theorem integral_norm_signedPackets_rpow {n m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (v x : Fin m → Space n) (c : Fin m → ℂ) (ε : Fin m → Bool)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (v i) (v j))
    {p : ℝ} (hp : 0 < p) :
    (∫ ω, ‖signedSum (fun i ↦ c i * capPacket δ (v i) (x i) ω) ε‖ ^ p
      ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n) =
      ∑ i, ‖c i‖ ^ p * (OAI.Analysis.Fourier.Restriction.sphereMeasure n).real (packetCap δ (v i)) := by
  simp_rw [norm_signedPackets_rpow hδ v x c ε hsep hp]
  rw [integral_finsetSum Finset.univ
    (fun i _ ↦ integrable_norm_mul_capPacket_rpow δ (v i) (x i) (c i) hp)]
  simp_rw [integral_norm_mul_capPacket_rpow δ _ _ _ hp]

theorem integrable_signedPackets {n m : ℕ} (δ : ℝ)
    (v x : Fin m → Space n) (c : Fin m → ℂ) (ε : Fin m → Bool) :
    Integrable (fun ω ↦ signedSum (fun i ↦ c i * capPacket δ (v i) (x i) ω) ε)
      (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  apply integrable_finsetSum
  intro i _
  cases hε : ε i
  · simpa [hε] using ((integrable_capPacket δ (v i) (x i)).const_mul (c i)).neg
  · simpa [hε] using (integrable_capPacket δ (v i) (x i)).const_mul (c i)

theorem memLp_signedPackets {n m : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (v x : Fin m → Space n) (c : Fin m → ℂ) (ε : Fin m → Bool)
    (hsep : ∀ i j, i ≠ j → δ ≤ dist (v i) (v j))
    {p : ℝ} (hp : 0 < p) :
    MemLp (fun ω ↦ signedSum (fun i ↦ c i * capPacket δ (v i) (x i) ω) ε)
      (ENNReal.ofReal p) (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
  have hm := (integrable_signedPackets δ v x c ε).aestronglyMeasurable
  apply (integrable_norm_rpow_iff hm (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top).mp
  simp only [ENNReal.toReal_ofReal hp.le]
  simp_rw [norm_signedPackets_rpow hδ v x c ε hsep hp]
  exact integrable_finsetSum Finset.univ
    (fun i _ ↦ integrable_norm_mul_capPacket_rpow δ (v i) (x i) (c i) hp)

theorem sphericalExtension_signedSum {n m : ℕ} (g : Fin m → Space n → ℂ)
    (hg : ∀ i, Integrable (g i) (OAI.Analysis.Fourier.Restriction.sphereMeasure n)) (ε : Fin m → Bool) (x : Space n) :
    OAI.Analysis.Fourier.Restriction.sphericalExtension (fun ω ↦ signedSum (fun i ↦ g i ω) ε) x =
      signedSum (fun i ↦ OAI.Analysis.Fourier.Restriction.sphericalExtension (g i) x) ε := by
  have hint (i : Fin m) : Integrable (fun ω ↦ if ε i then g i ω else -g i ω)
      (OAI.Analysis.Fourier.Restriction.sphereMeasure n) := by
    cases hε : ε i
    · simpa [hε] using (hg i).neg
    · simpa [hε] using hg i
  unfold signedSum
  rw [OAI.Analysis.Fourier.Restriction.sphericalExtension_sum Finset.univ _ (fun i _ ↦ hint i)]
  apply Finset.sum_congr rfl
  intro i _
  cases hε : ε i
  · simp only [Bool.false_eq_true, ↓reduceIte]
    simpa only [neg_one_mul] using OAI.Analysis.Fourier.Restriction.sphericalExtension_const_mul (-1) (g i) x
  · simp

/-- Exact second moment of independent random signs. -/
theorem sign_square_sum (m : ℕ) (z : Fin m → ℂ) :
    ∑ ε : Fin m → Bool, ‖signedSum z ε‖ ^ 2 = (2 : ℝ) ^ m * ∑ i, ‖z i‖ ^ 2 := by
  induction m with
  | zero => simp [signedSum]
  | succ m ih =>
    rw [sum_signs_succ]
    simp only [signedSum_cons]
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← Finset.sum_add_distrib]
    have hpar (ε : Fin m → Bool) :
        ‖z 0 + signedSum (fun i ↦ z i.succ) ε‖ ^ 2 +
          ‖-z 0 + signedSum (fun i ↦ z i.succ) ε‖ ^ 2 =
        2 * (‖z 0‖ ^ 2 + ‖signedSum (fun i ↦ z i.succ) ε‖ ^ 2) := by
      have h := parallelogram_law_with_norm ℂ (signedSum (fun i ↦ z i.succ) ε) (z 0)
      simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    simp_rw [hpar, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [ih]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat, Fin.sum_univ_succ, pow_succ]
    ring

theorem finite_average_rpow_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {q : ℝ} (hq : 1 ≤ q) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) :
    ((∑ i, a i) / Fintype.card ι) ^ q ≤ (∑ i, a i ^ q) / Fintype.card ι := by
  have hcard : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have hw : (∑ _i : ι, (Fintype.card ι : ℝ)⁻¹) = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcard.ne'
  have h := (convexOn_rpow hq).map_sum_le
    (t := Finset.univ) (w := fun _ : ι ↦ (Fintype.card ι : ℝ)⁻¹)
    (p := a) (fun _ _ ↦ inv_nonneg.mpr hcard.le) hw (fun i _ ↦ ha i)
  calc
    ((∑ i, a i) / Fintype.card ι) ^ q =
        ((Fintype.card ι : ℝ)⁻¹ * ∑ i, a i) ^ q := by congr 1; ring
    _ ≤ (Fintype.card ι : ℝ)⁻¹ * ∑ i, a i ^ q := by
      simpa only [smul_eq_mul, ← Finset.mul_sum] using h
    _ = (∑ i, a i ^ q) / Fintype.card ι := by ring

/-- The lower Khintchine estimate needed for the restriction-to-Kakeya
argument, with the exact finite average over all independent sign choices. -/
theorem sign_randomization_lower {m : ℕ} (z : Fin m → ℂ) {p : ℝ} (hp : 2 ≤ p) :
    (∑ i, ‖z i‖ ^ 2) ^ (p / 2) ≤
      (∑ ε : Fin m → Bool, ‖signedSum z ε‖ ^ p) / (2 : ℝ) ^ m := by
  have h := finite_average_rpow_le (by linarith : 1 ≤ p / 2)
    (fun ε : Fin m → Bool ↦ ‖signedSum z ε‖ ^ 2) (fun _ ↦ sq_nonneg _)
  have hcard : (Fintype.card (Fin m → Bool) : ℝ) = (2 : ℝ) ^ m := by simp
  rw [hcard, sign_square_sum] at h
  have hcancel : ((2 : ℝ) ^ m * ∑ i, ‖z i‖ ^ 2) / 2 ^ m = ∑ i, ‖z i‖ ^ 2 := by
    field_simp
  rw [hcancel] at h
  have hrpow (ε : Fin m → Bool) :
      (‖signedSum z ε‖ ^ 2) ^ (p / 2) = ‖signedSum z ε‖ ^ p := by
    rw [← Real.rpow_natCast_mul (norm_nonneg _) 2]
    congr 1
    push_cast
    ring
  simpa only [hrpow] using h

/-- Integrated randomization. Integrability of the square sum is a conclusion,
deduced from the finitely many signed estimates. This is the form used after
applying the spherical extension estimate to every sign choice. -/
theorem integral_sign_randomization_lower {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {m : ℕ} (z : Fin m → α → ℂ) {p : ℝ} (hp : 2 ≤ p)
    (hz : ∀ i, AEStronglyMeasurable (z i) μ)
    (hints : ∀ ε : Fin m → Bool,
      Integrable (fun x ↦ ‖signedSum (fun i ↦ z i x) ε‖ ^ p) μ) :
    Integrable (fun x ↦ (∑ i, ‖z i x‖ ^ 2) ^ (p / 2)) μ ∧
    (∫ x, (∑ i, ‖z i x‖ ^ 2) ^ (p / 2) ∂μ) ≤
      (∑ ε : Fin m → Bool, ∫ x, ‖signedSum (fun i ↦ z i x) ε‖ ^ p ∂μ) / (2 : ℝ) ^ m := by
  have hmean : Integrable
      (fun x ↦ (∑ ε : Fin m → Bool, ‖signedSum (fun i ↦ z i x) ε‖ ^ p) / (2 : ℝ) ^ m) μ :=
    (integrable_finsetSum Finset.univ (fun ε _ ↦ hints ε)).div_const _
  have hmeas : AEStronglyMeasurable (fun x ↦ (∑ i, ‖z i x‖ ^ 2) ^ (p / 2)) μ := by
    have hsum : AEStronglyMeasurable (fun x ↦ ∑ i, ‖z i x‖ ^ 2) μ := by fun_prop
    exact (Real.continuous_rpow_const (by linarith : 0 ≤ p / 2)).comp_aestronglyMeasurable hsum
  have hbound (x : α) : (∑ i, ‖z i x‖ ^ 2) ^ (p / 2) ≤
      (∑ ε : Fin m → Bool, ‖signedSum (fun i ↦ z i x) ε‖ ^ p) / (2 : ℝ) ^ m :=
    sign_randomization_lower (fun i ↦ z i x) hp
  have hi : Integrable (fun x ↦ (∑ i, ‖z i x‖ ^ 2) ^ (p / 2)) μ := by
    apply hmean.mono' hmeas
    exact Filter.Eventually.of_forall fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact hbound x
  refine ⟨hi, ?_⟩
  calc
    (∫ x, (∑ i, ‖z i x‖ ^ 2) ^ (p / 2) ∂μ) ≤
      ∫ x, (∑ ε : Fin m → Bool, ‖signedSum (fun i ↦ z i x) ε‖ ^ p) / (2 : ℝ) ^ m ∂μ :=
        integral_mono hi hmean hbound
    _ = _ := by
      rw [integral_div, integral_finsetSum Finset.univ (fun ε _ ↦ hints ε)]

end OAI.MeasureTheory.Kakeya
