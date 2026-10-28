import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Finite Support -/

namespace OAI.RepresentationTheory.Theta.FiniteSupport

noncomputable section

/-!
Finite-input bounds and denominator clearing for CompletedTheta. Compact support and
boundedness are derived from the concrete finite Bruhat space in PoissonAutomorphyData;
the denominator argument uses finite-adele integrality. No Poisson or
transformation law is used.
-/

open scoped Classical RestrictedProduct
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

section TestFunctions
variable {ι : Type*} [Fintype ι]
theorem finiteSchwartz_mem_iff (f : (ι → PoissonAutomorphyNormalizationData.AQf) → ℂ) :
    f ∈ PoissonAutomorphyNormalizationData.finiteSchwartz ι ↔ IsLocallyConstant f ∧ HasCompactSupport f := by
  constructor
  · intro hf
    induction hf using Submodule.span_induction with
    | mem f hf => exact hf
    | zero => exact ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
    | add f g _ _ hf hg => exact ⟨hf.1.add hg.1, hf.2.add hg.2⟩
    | smul c f _ hf =>
      exact ⟨hf.1.comp (fun z : ℂ => c * z), hf.2.smul_left⟩
  · intro hf
    exact Submodule.subset_span hf

theorem finiteSchwartz_continuous (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) : Continuous φ.val :=
  ((finiteSchwartz_mem_iff φ.val).mp φ.property).1.continuous

theorem finiteSchwartz_hasCompactSupport (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    HasCompactSupport φ.val :=
  ((finiteSchwartz_mem_iff φ.val).mp φ.property).2

theorem finiteSchwartz_bounded (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    ∃ C : ℝ, ∀ x, ‖φ.val x‖ ≤ C :=
  (finiteSchwartz_hasCompactSupport φ).exists_bound_of_continuous
    (finiteSchwartz_continuous φ)

end TestFunctions

abbrev FinitePlace := HeightOneSpectrum ℤ

def integralAdele : Subring PoissonAutomorphyNormalizationData.AQf where
  carrier := {a | ∀ v : FinitePlace, a v ∈ v.adicCompletionIntegers ℚ}
  zero_mem' v := (v.adicCompletionIntegers ℚ).zero_mem
  one_mem' v := (v.adicCompletionIntegers ℚ).one_mem
  add_mem' ha hb v := (v.adicCompletionIntegers ℚ).toSubring.add_mem (ha v) (hb v)
  mul_mem' ha hb v := (v.adicCompletionIntegers ℚ).toSubring.mul_mem (ha v) (hb v)
  neg_mem' ha v := (v.adicCompletionIntegers ℚ).toSubring.neg_mem (ha v)

theorem isOpen_integralAdele : IsOpen (integralAdele : Set PoissonAutomorphyNormalizationData.AQf) := by
  exact RestrictedProduct.isOpen_forall_mem
    (fun v : FinitePlace => Valued.isOpen_valuationSubring (v.adicCompletion ℚ))

theorem intCast_mem_integralAdele (n : ℤ) : (n : PoissonAutomorphyNormalizationData.AQf) ∈ integralAdele :=
  intCast_mem integralAdele n

theorem integer_multiple_integral {a : PoissonAutomorphyNormalizationData.AQf} (ha : a ∈ integralAdele) (n : ℤ) :
    (n : PoissonAutomorphyNormalizationData.AQf) * a ∈ integralAdele :=
  integralAdele.mul_mem (intCast_mem_integralAdele n) ha

theorem integral_multiple_of_dvd {a : PoissonAutomorphyNormalizationData.AQf} {n m : ℤ}
    (h : (n : PoissonAutomorphyNormalizationData.AQf) * a ∈ integralAdele) (hnm : n ∣ m) :
    (m : PoissonAutomorphyNormalizationData.AQf) * a ∈ integralAdele := by
  obtain ⟨k, rfl⟩ := hnm
  simpa only [Int.cast_mul, mul_assoc, mul_left_comm (n : PoissonAutomorphyNormalizationData.AQf) (k : PoissonAutomorphyNormalizationData.AQf)] using
    integer_multiple_integral h k

theorem exists_integer_multiple_integral (a : PoissonAutomorphyNormalizationData.AQf) :
    ∃ n : ℤ, n ≠ 0 ∧ (n : PoissonAutomorphyNormalizationData.AQf) * a ∈ integralAdele := by
  have hfinite : {v : FinitePlace | a v ∉ v.adicCompletionIntegers ℚ}.Finite := by
    exact Filter.eventually_cofinite.mp a.property
  choose d hd hda using
    (fun v : FinitePlace =>
      adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v))
  let n : ℤ := ∏ v ∈ hfinite.toFinset, d v
  refine ⟨n, ?_, ?_⟩
  · apply Finset.prod_ne_zero_iff.mpr
    intro v _
    exact nonZeroDivisors.ne_zero (hd v)
  · intro v
    change (n : v.adicCompletion ℚ) * a v ∈ v.adicCompletionIntegers ℚ
    by_cases hv : v ∈ hfinite.toFinset
    · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem d hv
      change n = d v * k at hk
      rw [hk, Int.cast_mul]
      have hdv : a v * (d v : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
        simpa only [Algebra.cast, eq_intCast] using hda v
      have hkv : (k : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
        simpa only [Algebra.cast, eq_intCast] using coe_mem_adicCompletionIntegers (K := ℚ) v k
      have h := (v.adicCompletionIntegers ℚ).mul_mem _ _ hdv hkv
      rw [mul_assoc, mul_comm (a v)] at h
      exact h
    · have ha : a v ∈ v.adicCompletionIntegers ℚ := by
        simpa using hv
      apply (v.adicCompletionIntegers ℚ).mul_mem _ _ _ ha
      simpa only [Algebra.cast, eq_intCast] using coe_mem_adicCompletionIntegers (K := ℚ) v n

theorem rational_integral_iff (q : ℚ) :
    algebraMap ℚ PoissonAutomorphyNormalizationData.AQf q ∈ integralAdele ↔ ∃ n : ℤ, (n : ℚ) = q := by
  constructor
  · intro h
    apply mem_integers_of_valuation_le_one (R := ℤ) (K := ℚ) q
    intro v
    simpa only [mem_adicCompletionIntegers, FiniteAdeleRing.algebraMap_apply,
      valuedAdicCompletion_eq_valuation'] using h v
  · rintro ⟨n, rfl⟩
    simpa only [map_intCast] using intCast_mem_integralAdele n

variable {ι : Type*} [Fintype ι]

def integralBox (n : ℤ) : Set (ι → PoissonAutomorphyNormalizationData.AQf) :=
  {a | ∀ i, (n : PoissonAutomorphyNormalizationData.AQf) * a i ∈ integralAdele}

theorem isOpen_integralBox (n : ℤ) : IsOpen (integralBox (ι := ι) n) := by
  simp only [integralBox, Set.ofPred_forall]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_integralAdele.preimage (continuous_const.mul (continuous_apply i))

omit [Fintype ι] in
theorem integralBox_mono {n m : ℤ} (h : n ∣ m) :
    integralBox (ι := ι) n ⊆ integralBox m := by
  intro a ha i
  exact integral_multiple_of_dvd (ha i) h

theorem exists_integralBox (a : ι → PoissonAutomorphyNormalizationData.AQf) :
    ∃ n : ℤ, n ≠ 0 ∧ a ∈ integralBox n := by
  choose n hn ha using fun i => exists_integer_multiple_integral (a i)
  refine ⟨∏ i, n i, Finset.prod_ne_zero_iff.mpr (fun i _ => hn i), ?_⟩
  intro i
  exact integral_multiple_of_dvd (ha i) (Finset.dvd_prod_of_mem n (Finset.mem_univ i))

/-- A compact finite-adelic set has one denominator valid for every coordinate. -/
theorem compact_subset_integralBox (K : Set (ι → PoissonAutomorphyNormalizationData.AQf)) (hK : IsCompact K) :
    ∃ n : ℤ, n ≠ 0 ∧ K ⊆ integralBox n := by
  let U := fun n : {n : ℤ // n ≠ 0} => integralBox (ι := ι) n.val
  let : Nonempty {n : ℤ // n ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  have hcover : K ⊆ ⋃ n, U n := by
    intro a _
    obtain ⟨n, hn, ha⟩ := exists_integralBox a
    exact Set.mem_iUnion.mpr ⟨⟨n, hn⟩, ha⟩
  have hdir : Directed (· ⊆ ·) U := by
    intro n m
    refine ⟨⟨n.val * m.val, mul_ne_zero n.property m.property⟩, ?_, ?_⟩
    · exact integralBox_mono (dvd_mul_right n.val m.val)
    · exact integralBox_mono (dvd_mul_left m.val n.val)
  obtain ⟨n, hn⟩ := hK.elim_directed_cover U (fun n => isOpen_integralBox n.val) hcover hdir
  exact ⟨n.val, n.property, hn⟩

/-- Rational positions in finite Schwartz support have uniformly bounded denominators. -/
theorem finiteSchwartz_denominator (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ x : ι → ℚ,
      φ.val (PoissonAutomorphyNormalizationData.finiteDiagonal x) ≠ 0 → ∀ i, ∃ m : ℤ, (m : ℚ) = (n : ℚ) * x i := by
  obtain ⟨n, hn, hK⟩ := compact_subset_integralBox (tsupport φ.val)
    (finiteSchwartz_hasCompactSupport φ)
  refine ⟨n, hn, ?_⟩
  intro x hx i
  have h := hK (subset_tsupport φ.val hx) i
  apply (rational_integral_iff ((n : ℚ) * x i)).mp
  simpa only [PoissonAutomorphyNormalizationData.finiteDiagonal, map_mul, map_intCast] using h

/-- A positive common denominator for the rational support. -/
theorem finiteSchwartz_positive_denominator (Φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    ∃ N : ℕ, 0 < N ∧ ∀ x : ι → ℚ,
      Φ.val (PoissonAutomorphyNormalizationData.finiteDiagonal x) ≠ 0 → ∀ i, ∃ m : ℤ, (m : ℚ) = (N : ℚ) * x i := by
  obtain ⟨n, hn, hden⟩ := finiteSchwartz_denominator Φ
  obtain ⟨k, hk⟩ : n ∣ (n.natAbs : ℤ) := Int.dvd_natAbs.mpr (dvd_refl n)
  refine ⟨n.natAbs, Int.natAbs_pos.mpr hn, ?_⟩
  intro x hx i
  obtain ⟨m, hm⟩ := hden x hx i
  refine ⟨k * m, ?_⟩
  have hkq : (n.natAbs : ℚ) = (n : ℚ) * (k : ℚ) := by
    simpa only [Int.cast_natCast, Int.cast_mul] using congrArg (fun z : ℤ => (z : ℚ)) hk
  rw [Int.cast_mul, hm, hkq]
  ring

/-- The least positive common denominator of the rational support. -/
def supportDenominator (Φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) : ℕ :=
  Nat.find (finiteSchwartz_positive_denominator Φ)

theorem supportDenominator_spec (Φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    0 < supportDenominator Φ ∧ ∀ x : ι → ℚ,
      Φ.val (PoissonAutomorphyNormalizationData.finiteDiagonal x) ≠ 0 → ∀ i, ∃ m : ℤ,
        (m : ℚ) = (supportDenominator Φ : ℚ) * x i :=
  Nat.find_spec (finiteSchwartz_positive_denominator Φ)

end

end OAI.RepresentationTheory.Theta.FiniteSupport
