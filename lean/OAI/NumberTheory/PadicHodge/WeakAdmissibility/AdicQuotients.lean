import Mathlib

/-! # Adic Quotients -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.AdicQuotients

noncomputable section

/-!
Adic completeness of quotients by elements regular modulo the adic parameter.
The hypotheses are algebraic conditions, discharged for the theta generator
in the concrete Fontaine ring.
-/

variable {R : Type*} [CommRing R]

theorem pow_dvd_cancel_factor [IsDomain R] (q c : R) (hq : q ≠ 0)
    (hbase : ∀ z : R, q ∣ c * z → q ∣ z) (n : ℕ) (z : R)
    (hz : q ^ n ∣ c * z) : q ^ n ∣ z := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    obtain ⟨u, hu⟩ := hbase z ((dvd_pow_self q (Nat.succ_ne_zero n)).trans hz)
    obtain ⟨w, hw⟩ := hz
    have hcu : c * u = q ^ n * w := by
      apply mul_left_cancel₀ hq
      calc
        q * (c * u) = c * (q * u) := by ring
        _ = c * z := by rw [← hu]
        _ = q ^ (n + 1) * w := hw
        _ = q * (q ^ n * w) := by rw [pow_succ]; ring
    obtain ⟨v, hv⟩ := ih u ⟨w, hcu⟩
    refine ⟨v, ?_⟩
    rw [hu, hv, pow_succ]
    ring

/-- Cancellation modulo every q-power makes a principal ideal q-adically closed. -/
theorem mem_span_of_approx (q c : R) [IsAdicComplete (Ideal.span {q}) R]
    (hcancel : ∀ n : ℕ, ∀ z : R,
      c * z ∈ (Ideal.span {q}) ^ n → z ∈ (Ideal.span {q}) ^ n)
    (x : R) (hx : ∀ n : ℕ, ∃ y : R, x - c * y ∈ (Ideal.span {q}) ^ n) :
    x ∈ Ideal.span {c} := by
  classical
  choose y hy using hx
  let I : Ideal R := Ideal.span {q}
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      y m ≡ y n [SMOD (I ^ m • ⊤ : Submodule R R)] := by
    intro m n hmn
    have hmul : c * (y m - y n) ∈ I ^ m := by
      have he : c * (y m - y n) = (x - c * y n) - (x - c * y m) := by ring
      rw [he]
      exact Ideal.sub_mem _ (Ideal.pow_le_pow_right hmn (hy n)) (hy m)
    simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hcancel m (y m - y n) hmul
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (show IsPrecomplete I R from inferInstance) hcauchy
  have hzero : x - c * L = 0 := by
    apply IsHausdorff.haus (show IsHausdorff I R from inferInstance)
    intro n
    have hdiff : y n - L ∈ I ^ n := by
      simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hL n
    have he : x - c * L = (x - c * y n) + c * (y n - L) := by ring
    have hmem : x - c * L ∈ I ^ n := by
      rw [he]
      exact Ideal.add_mem _ (hy n) (Ideal.mul_mem_left _ _ hdiff)
    simpa only [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top] using hmem
  exact Ideal.mem_span_singleton.mpr ⟨L, sub_eq_zero.mp hzero⟩

def adicSeries (q : R) (a : ℕ → R) (n : ℕ) : R := ∑ i ∈ Finset.range n, q ^ i * a i

theorem adicSeries_succ (q : R) (a : ℕ → R) (n : ℕ) :
    adicSeries q a (n + 1) = adicSeries q a n + q ^ n * a n := Finset.sum_range_succ _ n

theorem adicSeries_cauchy (q : R) (a : ℕ → R) {m n : ℕ} (hmn : m ≤ n) :
    adicSeries q a m ≡ adicSeries q a n
      [SMOD ((Ideal.span {q}) ^ m • ⊤ : Submodule R R)] := by
  change (Submodule.mkQ _) (adicSeries q a m) = (Submodule.mkQ _) (adicSeries q a n)
  rw [adicSeries, adicSeries, map_sum, map_sum]
  apply Finset.sum_subset (Finset.range_mono hmn)
  intro i _ hi
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  have hmi : m ≤ i := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hi)
  have hmem : q ^ i * a i ∈ (Ideal.span {q}) ^ m := by
    apply Ideal.pow_le_pow_right hmi
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) i)
  simpa only [smul_eq_mul, Ideal.mul_top] using hmem

theorem exists_adicSeries_limit (q : R) [IsPrecomplete (Ideal.span {q}) R] (a : ℕ → R) :
    ∃ L : R, ∀ n : ℕ, adicSeries q a n ≡ L
      [SMOD ((Ideal.span {q}) ^ n • ⊤ : Submodule R R)] :=
  IsPrecomplete.prec inferInstance (adicSeries_cauchy q a)

/-- Every quotient of a q-adically precomplete ring is q-adically precomplete. -/
theorem quotient_isPrecomplete (q : R) (J : Ideal R) [IsPrecomplete (Ideal.span {q}) R] :
    IsPrecomplete (Ideal.span {Ideal.Quotient.mk J q}) (R ⧸ J) := by
  classical
  constructor
  intro f hf
  have hstep (n : ℕ) : ∃ a : R ⧸ J,
      f (n + 1) - f n = (Ideal.Quotient.mk J q) ^ n * a := by
    have hmem : f (n + 1) - f n ∈ (Ideal.span {Ideal.Quotient.mk J q}) ^ n := by
      simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using (hf (Nat.le_succ n)).symm
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    exact hmem
  choose a ha using hstep
  choose b hb using fun n : ℕ => Ideal.Quotient.mk_surjective (a n)
  obtain ⟨r₀, hr₀⟩ := Ideal.Quotient.mk_surjective (f 0)
  have hs (n : ℕ) : Ideal.Quotient.mk J (r₀ + adicSeries q b n) = f n := by
    induction n with
    | zero => simpa only [adicSeries, Finset.range_zero, Finset.sum_empty, add_zero] using hr₀
    | succ n ih =>
      calc
        Ideal.Quotient.mk J (r₀ + adicSeries q b (n + 1)) =
            Ideal.Quotient.mk J (r₀ + adicSeries q b n) +
              (Ideal.Quotient.mk J q) ^ n * Ideal.Quotient.mk J (b n) := by
          simp only [adicSeries_succ, map_add, map_mul, map_pow]
          ring
        _ = f n + (Ideal.Quotient.mk J q) ^ n * a n := by rw [ih, hb]
        _ = f (n + 1) := by linear_combination -(ha n)
  obtain ⟨L, hL⟩ := exists_adicSeries_limit q b
  refine ⟨Ideal.Quotient.mk J (r₀ + L), fun n => ?_⟩
  have hdiff : adicSeries q b n - L ∈ (Ideal.span {q}) ^ n := by
    simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hL n
  have hmap := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hdiff
  simp only [Ideal.map_pow, Ideal.map_span, Set.image_singleton] at hmap
  have he : f n - Ideal.Quotient.mk J (r₀ + L) =
      Ideal.Quotient.mk J (adicSeries q b n - L) := by
    rw [← hs n]
    simp only [map_add, map_sub]
    ring
  simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, he] using hmap

/-- A principal quotient is Hausdorff when multiplication by its generator
cancels modulo each q-power. -/
theorem quotient_isHausdorff (q c : R) [IsAdicComplete (Ideal.span {q}) R]
    (hcancel : ∀ n : ℕ, ∀ z : R,
      c * z ∈ (Ideal.span {q}) ^ n → z ∈ (Ideal.span {q}) ^ n) :
    IsHausdorff (Ideal.span {Ideal.Quotient.mk (Ideal.span {c}) q}) (R ⧸ Ideal.span {c}) := by
  constructor
  intro z hz
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective z
  have happrox (n : ℕ) : ∃ y : R, x - c * y ∈ (Ideal.span {q}) ^ n := by
    have hmem : z ∈ (Ideal.span {Ideal.Quotient.mk (Ideal.span {c}) q}) ^ n := by
      simpa only [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top] using hz n
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
    obtain ⟨a, ha⟩ := hmem
    obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective a
    have hker : Ideal.Quotient.mk (Ideal.span {c}) (x - q ^ n * v) = 0 := by
      simp only [map_sub, map_mul, map_pow, hx, hv, ha, sub_self]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hker)
    refine ⟨y, ?_⟩
    have he : x - c * y = q ^ n * v := by linear_combination hy
    rw [he]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) n)
  have hmem := mem_span_of_approx q c hcancel x happrox
  exact hx.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hmem)

/-- Completeness of a principal quotient under the proved cancellation condition. -/
theorem quotient_isAdicComplete (q c : R) [IsAdicComplete (Ideal.span {q}) R]
    (hcancel : ∀ n : ℕ, ∀ z : R,
      c * z ∈ (Ideal.span {q}) ^ n → z ∈ (Ideal.span {q}) ^ n) :
    IsAdicComplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {c}) q}) (R ⧸ Ideal.span {c}) where
  toIsHausdorff := quotient_isHausdorff q c hcancel
  toIsPrecomplete := quotient_isPrecomplete q (Ideal.span {c})

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.AdicQuotients
