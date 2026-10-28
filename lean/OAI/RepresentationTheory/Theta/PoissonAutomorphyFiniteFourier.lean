import OAI.RepresentationTheory.Theta.IntegralAdeles
import Mathlib.Data.Nat.ChineseRemainder

/-! # Poisson Automorphy Finite Fourier -/

namespace OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction

noncomputable section

section

/-! Simultaneous integral approximation in distinct p-adic integer rings. -/

open scoped Classical

instance primeFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

variable {I : Type*} (p : I → Nat.Primes)

abbrev PadicFamily := ∀ i : I, PadicInt (p i).val

theorem finite_padic_approximation (hp : Function.Injective p)
    (s : Finset I) (a : PadicFamily p) (k : I → ℕ) :
    ∃ m : ℤ, ∀ i ∈ s,
      ‖(m : PadicInt (p i).val) - a i‖ ≤ ((p i).val : ℝ) ^ (-(k i : ℤ)) := by
  have hcop : Set.Pairwise (s : Set I)
      (Function.onFun Nat.Coprime (fun i => (p i).val ^ k i)) := by
    intro i _ j _ hij
    apply Nat.coprime_pow_primes _ _ (p i).property (p j).property
    intro heq
    exact hij (hp (Subtype.ext heq))
  let m := Nat.chineseRemainderOfFinset
    (fun i => (a i).appr (k i)) (fun i => (p i).val ^ k i) s
    (fun i _ => pow_ne_zero _ (p i).property.ne_zero) hcop
  refine ⟨m.val, ?_⟩
  intro i hi
  have hdiv : (((p i).val : ℤ) ^ k i) ∣ (m.val : ℤ) - ((a i).appr (k i) : ℤ) := by
    simpa only [Nat.cast_pow] using (m.property i hi).symm.dvd
  have h₁ : ‖(m.val : PadicInt (p i).val) - ((a i).appr (k i) : PadicInt (p i).val)‖ ≤
      ((p i).val : ℝ) ^ (-(k i : ℤ)) := by
    have h := (PadicInt.norm_int_le_pow_iff_dvd (p := (p i).val)).mpr hdiv
    simpa only [Int.cast_sub, Int.cast_natCast] using h
  have h₂ : ‖((a i).appr (k i) : PadicInt (p i).val) - a i‖ ≤
      ((p i).val : ℝ) ^ (-(k i : ℤ)) := by
    rw [norm_sub_rev, PadicInt.norm_le_pow_iff_mem_span_pow]
    exact (a i).appr_spec (k i)
  have h := (PadicInt.nonarchimedean
    ((m.val : PadicInt (p i).val) - ((a i).appr (k i) : PadicInt (p i).val))
    (((a i).appr (k i) : PadicInt (p i).val) - a i)).trans (max_le h₁ h₂)
  simpa only [sub_add_sub_cancel, Int.cast_natCast] using h

theorem denseRange_integer_padicFamily (hp : Function.Injective p) :
    DenseRange (fun m : ℤ => fun i : I => (m : PadicInt (p i).val)) := by
  intro a
  rw [mem_closure_iff]
  intro U hU ha
  obtain ⟨s, u, hu, hsub⟩ := isOpen_pi_iff.mp hU a ha
  have hprecision : ∀ i : I, ∃ k : ℕ, i ∈ s →
      ∀ z : PadicInt (p i).val,
        ‖z - a i‖ ≤ ((p i).val : ℝ) ^ (-(k : ℤ)) → z ∈ u i := by
    intro i
    by_cases hi : i ∈ s
    · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hu i hi).1 (a i) (hu i hi).2
      obtain ⟨k, hk⟩ := PadicInt.exists_pow_neg_lt (p i).val hε
      refine ⟨k, fun _ z hz => hball ?_⟩
      rw [Metric.mem_ball, dist_eq_norm]
      exact hz.trans_lt hk
    · exact ⟨0, fun h => (hi h).elim⟩
  choose k hk using hprecision
  obtain ⟨m, hm⟩ := finite_padic_approximation p hp s a k
  refine ⟨(fun i => (m : PadicInt (p i).val)), hsub ?_, Set.mem_range_self m⟩
  intro i hi
  exact hk i hi _ (hm i hi)

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

def localPadicHomeomorph (v : AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) :
    PadicInt (Rat.HeightOneSpectrum.primesEquiv v).val ≃ₜ v.adicCompletionIntegers ℚ := by
  let : Algebra ℤ (v.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  exact (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).toHomeomorph.symm

theorem localPadicHomeomorph_intCast (v : AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) (n : ℤ) :
    localPadicHomeomorph v n = n := by
  let : Algebra ℤ (v.adicCompletionIntegers ℚ) := Ring.toIntAlgebra _
  exact map_intCast (Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v).symm n

def integralPadicHomeomorph :
    PadicFamily (Rat.HeightOneSpectrum.primesEquiv : AdelicSupport.PoissonAutomorphyConstruction.FinitePlace ≃ Nat.Primes) ≃ₜ AdelicSupport.PoissonAutomorphyConstruction.integralAdele :=
  (Homeomorph.piCongrRight localPadicHomeomorph).trans IntegralAdeles.PoissonAutomorphyConstruction.integralProductHomeomorph

theorem integralPadicHomeomorph_intCast (n : ℤ) :
    integralPadicHomeomorph (fun v => (n : PadicInt
      (Rat.HeightOneSpectrum.primesEquiv v).val)) = (n : AdelicSupport.PoissonAutomorphyConstruction.integralAdele) := by
  apply Subtype.ext
  apply Subtype.ext
  funext v
  change (localPadicHomeomorph v n).val = _
  rw [localPadicHomeomorph_intCast]
  rfl

theorem denseRange_integer_integralAdele :
    DenseRange (fun n : ℤ => (n : AdelicSupport.PoissonAutomorphyConstruction.integralAdele)) := by
  have h := integralPadicHomeomorph.surjective.denseRange.comp
    (denseRange_integer_padicFamily Rat.HeightOneSpectrum.primesEquiv
      Rat.HeightOneSpectrum.primesEquiv.injective) integralPadicHomeomorph.continuous
  simpa only [Function.comp_def, integralPadicHomeomorph_intCast] using h

theorem denseRange_rational_finiteAdele : DenseRange (algebraMap ℚ PoissonAutomorphyNormalizationData.AQf) := by
  let S := (algebraMap ℚ PoissonAutomorphyNormalizationData.AQf).range
  have hO : ∀ a : AdelicSupport.PoissonAutomorphyConstruction.integralAdele, a.val ∈ S.topologicalClosure := by
    intro a
    refine denseRange_integer_integralAdele.induction_on
      (p := fun a : AdelicSupport.PoissonAutomorphyConstruction.integralAdele => a.val ∈ S.topologicalClosure) a
      (S.isClosed_topologicalClosure.preimage continuous_subtype_val) ?_
    intro n
    apply S.le_topologicalClosure
    exact ⟨n, by simp⟩
  intro a
  obtain ⟨n, hn, hna⟩ := AdelicSupport.PoissonAutomorphyConstruction.exists_integer_multiple_integral a
  have hid : algebraMap ℚ PoissonAutomorphyNormalizationData.AQf ((n : ℚ)⁻¹) * (n : PoissonAutomorphyNormalizationData.AQf) = 1 := by
    rw [← map_intCast (algebraMap ℚ PoissonAutomorphyNormalizationData.AQf) n, ← map_mul,
      inv_mul_cancel₀ (by exact_mod_cast hn), map_one]
  have ha : a ∈ S.topologicalClosure := by
    have h := S.topologicalClosure.mul_mem
      (S.le_topologicalClosure (Set.mem_range_self ((n : ℚ)⁻¹)))
      (hO ⟨(n : PoissonAutomorphyNormalizationData.AQf) * a, hna⟩)
    simpa only [← mul_assoc, hid, one_mul] using h
  exact ha

end

section

/-! The specified adelic character has conductor equal to the integral finite adeles. -/

open scoped Classical

theorem standardRealCharacter_intCast (n : ℤ) :
    PoissonAutomorphyNormalizationData.standardRealCharacter n = 1 := by
  rw [PoissonAutomorphyNormalizationData.standardRealCharacter_apply]
  simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_intCast,
    mul_assoc, mul_comm, mul_left_comm] using Complex.exp_int_mul_two_pi_mul_I n

theorem standardRealCharacter_eq_one_iff (t : ℝ) :
    PoissonAutomorphyNormalizationData.standardRealCharacter t = 1 ↔ ∃ n : ℤ, (n : ℝ) = t := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    refine ⟨n, ?_⟩
    have hi := congrArg Complex.im hn
    simp [Complex.mul_im] at hi
    have ht : (2 * Real.pi) * t = (2 * Real.pi) * (n : ℝ) := by
      convert hi using 1
      ring
    exact (mul_left_cancel₀ (by positivity) ht).symm
  · rintro ⟨n, rfl⟩
    exact standardRealCharacter_intCast n

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

theorem finiteCharacter_continuous : Continuous D.finiteCharacter := by
  have h : (D.finiteCharacter : PoissonAutomorphyNormalizationData.AQf → ℂ) = fun a => D.character (0, a) :=
    funext D.finiteCharacter_eq
  rw [h]
  exact D.character_continuous.comp (continuous_const.prodMk continuous_id)

theorem character_split (t : ℝ) (a : PoissonAutomorphyNormalizationData.AQf) :
    D.character (t, a) = PoissonAutomorphyNormalizationData.standardRealCharacter t * D.finiteCharacter a := by
  rw [D.finiteCharacter_eq, ← D.character_real, ← AddChar.map_add_eq_mul]
  simp

theorem character_rational_product (q : ℚ) :
    PoissonAutomorphyNormalizationData.standardRealCharacter q * D.finiteCharacter (algebraMap ℚ PoissonAutomorphyNormalizationData.AQf q) = 1 := by
  rw [← character_split]
  exact D.character_rational q

theorem finiteCharacter_intCast (n : ℤ) : D.finiteCharacter (n : PoissonAutomorphyNormalizationData.AQf) = 1 := by
  have h := character_rational_product D (n : ℚ)
  simpa only [Rat.cast_intCast, map_intCast, standardRealCharacter_intCast, one_mul] using h

theorem finiteCharacter_integral (a : PoissonAutomorphyNormalizationData.AQf) (ha : a ∈ AdelicSupport.PoissonAutomorphyConstruction.integralAdele) :
    D.finiteCharacter a = 1 := by
  have h := denseRange_integer_integralAdele.equalizer
    ((finiteCharacter_continuous D).comp continuous_subtype_val)
    (continuous_const : Continuous (fun _ : AdelicSupport.PoissonAutomorphyConstruction.integralAdele => (1 : ℂ)))
    (funext fun n => finiteCharacter_intCast D n)
  exact congrFun h ⟨a, ha⟩

theorem finiteAdele_rational_representative (a : PoissonAutomorphyNormalizationData.AQf) :
    ∃ q : ℚ, a - algebraMap ℚ PoissonAutomorphyNormalizationData.AQf q ∈ AdelicSupport.PoissonAutomorphyConstruction.integralAdele := by
  obtain ⟨q, hq⟩ := denseRange_rational_finiteAdele.exists_mem_open
    (s := {b : PoissonAutomorphyNormalizationData.AQf | a - b ∈ AdelicSupport.PoissonAutomorphyConstruction.integralAdele})
    (AdelicSupport.PoissonAutomorphyConstruction.isOpen_integralAdele.preimage (continuous_const.sub continuous_id))
    ⟨a, by simp⟩
  exact ⟨q, hq⟩

theorem finiteCharacter_eq_one_iff (a : PoissonAutomorphyNormalizationData.AQf) :
    D.finiteCharacter a = 1 ↔ a ∈ AdelicSupport.PoissonAutomorphyConstruction.integralAdele := by
  refine ⟨fun ha => ?_, finiteCharacter_integral D a⟩
  obtain ⟨q, hq⟩ := finiteAdele_rational_representative a
  have hqchar : D.finiteCharacter (algebraMap ℚ PoissonAutomorphyNormalizationData.AQf q) = 1 := by
    have h := D.finiteCharacter.map_add_eq_mul (a - algebraMap ℚ PoissonAutomorphyNormalizationData.AQf q)
      (algebraMap ℚ PoissonAutomorphyNormalizationData.AQf q)
    rw [sub_add_cancel, ha, finiteCharacter_integral D _ hq, one_mul] at h
    exact h.symm
  have hr := character_rational_product D q
  rw [hqchar, mul_one] at hr
  obtain ⟨n, hn⟩ := (standardRealCharacter_eq_one_iff (q : ℝ)).mp hr
  have hnq : (n : ℚ) = q := by exact_mod_cast hn
  have hqi : algebraMap ℚ PoissonAutomorphyNormalizationData.AQf q ∈ AdelicSupport.PoissonAutomorphyConstruction.integralAdele := by
    rw [← hnq, map_intCast]
    exact intCast_mem AdelicSupport.PoissonAutomorphyConstruction.integralAdele n
  simpa only [sub_add_cancel] using AdelicSupport.PoissonAutomorphyConstruction.integralAdele.add_mem hq hqi

end

section

/-! The self-dual finite Haar measure gives the integral lattice volume one. -/

open scoped Classical
open _root_.MeasureTheory

instance localCompletionT2Space (v : AdelicSupport.PoissonAutomorphyConstruction.FinitePlace) : T2Space (v.adicCompletion ℚ) :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv v).toHomeomorph.isEmbedding.t2Space

instance finiteAdeleT2Space : T2Space PoissonAutomorphyNormalizationData.AQf := by
  exact T2Space.of_injective_continuous
    (f := fun a : PoissonAutomorphyNormalizationData.AQf => fun v : AdelicSupport.PoissonAutomorphyConstruction.FinitePlace => a v)
    DFunLike.coe_injective RestrictedProduct.continuous_coe

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def integralVectors : Subring (ι → PoissonAutomorphyNormalizationData.AQf) where
  carrier := {x | ∀ i, x i ∈ AdelicSupport.PoissonAutomorphyConstruction.integralAdele}
  zero_mem' := fun _ => AdelicSupport.PoissonAutomorphyConstruction.integralAdele.zero_mem
  one_mem' := fun _ => AdelicSupport.PoissonAutomorphyConstruction.integralAdele.one_mem
  add_mem' hx hy i := AdelicSupport.PoissonAutomorphyConstruction.integralAdele.add_mem (hx i) (hy i)
  mul_mem' hx hy i := AdelicSupport.PoissonAutomorphyConstruction.integralAdele.mul_mem (hx i) (hy i)
  neg_mem' hx i := AdelicSupport.PoissonAutomorphyConstruction.integralAdele.neg_mem (hx i)

omit [Fintype ι] [DecidableEq ι] in
theorem integralVectors_isCompact : IsCompact (integralVectors (ι := ι) : Set (ι → PoissonAutomorphyNormalizationData.AQf)) :=
  isCompact_pi_infinite (fun _ => IntegralAdeles.PoissonAutomorphyConstruction.isCompact_integralAdele)

omit [DecidableEq ι] in
theorem integralVectors_isOpen : IsOpen (integralVectors (ι := ι) : Set (ι → PoissonAutomorphyNormalizationData.AQf)) := by
  change IsOpen {x : ι → PoissonAutomorphyNormalizationData.AQf | ∀ i, x i ∈ AdelicSupport.PoissonAutomorphyConstruction.integralAdele}
  convert isOpen_iInter_of_finite
    (fun i : ι => AdelicSupport.PoissonAutomorphyConstruction.isOpen_integralAdele.preimage (continuous_apply i)) using 1
  ext x
  simp

omit [DecidableEq ι] in
theorem integralVectors_isClopen : IsClopen (integralVectors (ι := ι) : Set (ι → PoissonAutomorphyNormalizationData.AQf)) :=
  ⟨integralVectors_isCompact.isClosed, integralVectors_isOpen⟩

def integralIndicator (x : ι → PoissonAutomorphyNormalizationData.AQf) : ℂ :=
  (integralVectors (ι := ι) : Set (ι → PoissonAutomorphyNormalizationData.AQf)).indicator (fun _ => 1) x

omit [Fintype ι] [DecidableEq ι] in
theorem integralIndicator_of_mem {x : ι → PoissonAutomorphyNormalizationData.AQf} (hx : x ∈ integralVectors) :
    integralIndicator x = 1 := Set.indicator_of_mem hx _

omit [Fintype ι] [DecidableEq ι] in
theorem integralIndicator_of_notMem {x : ι → PoissonAutomorphyNormalizationData.AQf} (hx : x ∉ integralVectors) :
    integralIndicator x = 0 := Set.indicator_of_notMem hx _

def integralTestFunction : PoissonAutomorphyNormalizationData.finiteSchwartz ι := by
  refine ⟨integralIndicator, (PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff _).mpr ⟨?_, ?_⟩⟩
  · exact ((LocallyConstant.const (ι → PoissonAutomorphyNormalizationData.AQf) (1 : ℂ)).indicator
      integralVectors_isClopen).isLocallyConstant
  · apply integralVectors_isCompact.of_isClosed_subset isClosed_closure
    apply closure_minimal _ integralVectors_isCompact.isClosed
    exact Set.support_indicator_subset

omit [Fintype ι] [DecidableEq ι] in
theorem integralIndicator_add {u : ι → PoissonAutomorphyNormalizationData.AQf} (hu : u ∈ integralVectors) (y : ι → PoissonAutomorphyNormalizationData.AQf) :
    integralIndicator (u + y) = integralIndicator y := by
  have hmem : u + y ∈ integralVectors ↔ y ∈ integralVectors := by
    constructor
    · intro h
      simpa only [add_sub_cancel_left] using integralVectors.sub_mem h hu
    · exact integralVectors.add_mem hu
  simp only [integralIndicator, Set.indicator, SetLike.mem_coe, hmem]

variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

theorem finiteCharacter_pairing_integral {x y : ι → PoissonAutomorphyNormalizationData.AQf}
    (hx : x ∈ integralVectors) (hy : y ∈ integralVectors) :
    D.finiteCharacter (-(∑ i, x i * y i)) = 1 := by
  apply finiteCharacter_integral D
  exact AdelicSupport.PoissonAutomorphyConstruction.integralAdele.neg_mem (AdelicSupport.PoissonAutomorphyConstruction.integralAdele.sum_mem (fun i _ => AdelicSupport.PoissonAutomorphyConstruction.integralAdele.mul_mem
    (hx i) (hy i)))

theorem integralIndicator_fourier_of_mem {x : ι → PoissonAutomorphyNormalizationData.AQf} (hx : x ∈ integralVectors) :
    PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure integralIndicator x =
      (D.finiteMeasure.real (integralVectors (ι := ι) : Set (ι → PoissonAutomorphyNormalizationData.AQf)) : ℂ) := by
  have heq : (fun y : ι → PoissonAutomorphyNormalizationData.AQf => integralIndicator y *
      D.finiteCharacter (-(∑ i, x i * y i))) = integralIndicator := by
    funext y
    by_cases hy : y ∈ integralVectors
    · rw [integralIndicator_of_mem hy, finiteCharacter_pairing_integral D hx hy, one_mul]
    · rw [integralIndicator_of_notMem hy, zero_mul]
  rw [PoissonAutomorphyNormalizationData.fourier, heq]
  change (∫ y, (integralVectors (ι := ι) : Set (ι → PoissonAutomorphyNormalizationData.AQf)).indicator
    (fun _ => (1 : ℂ)) y ∂D.finiteMeasure) = _
  have hmeas : MeasurableSet (integralVectors (ι := ι) : Set (ι → PoissonAutomorphyNormalizationData.AQf)) := by
    change MeasurableSet {x : ι → PoissonAutomorphyNormalizationData.AQf | ∀ i, x i ∈ AdelicSupport.PoissonAutomorphyConstruction.integralAdele}
    convert MeasurableSet.iInter (fun i : ι =>
      AdelicSupport.PoissonAutomorphyConstruction.isOpen_integralAdele.measurableSet.preimage (measurable_pi_apply i)) using 1
    ext x
    simp
  rw [integral_indicator hmeas]
  simp

theorem integralIndicator_fourier_of_notMem {x : ι → PoissonAutomorphyNormalizationData.AQf} (hx : x ∉ integralVectors) :
    PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure integralIndicator x = 0 := by
  let := D.finiteMeasure_haar
  obtain ⟨i, hi⟩ : ∃ i, x i ∉ AdelicSupport.PoissonAutomorphyConstruction.integralAdele := not_forall.mp hx
  let u : ι → PoissonAutomorphyNormalizationData.AQf := Pi.single i 1
  have hu : u ∈ integralVectors := by
    intro j
    by_cases hj : j = i <;> simp [u, hj, AdelicSupport.PoissonAutomorphyConstruction.integralAdele.one_mem, AdelicSupport.PoissonAutomorphyConstruction.integralAdele.zero_mem]
  have hphase : D.finiteCharacter (-(∑ j, x j * u j)) ≠ 1 := by
    rw [show (∑ j, x j * u j) = x i from dotProduct_single_one x i]
    intro h
    exact hi (AdelicSupport.PoissonAutomorphyConstruction.integralAdele.neg_mem_iff.mp ((finiteCharacter_eq_one_iff D _).mp h))
  let F := fun y : ι → PoissonAutomorphyNormalizationData.AQf => integralIndicator y * D.finiteCharacter (-(∑ j, x j * y j))
  have hshift : ∀ y, F (u + y) = D.finiteCharacter (-(∑ j, x j * u j)) * F y := by
    intro y
    dsimp [F]
    rw [integralIndicator_add hu]
    simp only [mul_add, Finset.sum_add_distrib, neg_add,
      AddChar.map_add_eq_mul]
    ring
  have h := integral_add_left_eq_self (μ := D.finiteMeasure) F u
  simp_rw [hshift, integral_const_mul] at h
  change D.finiteCharacter (-(∑ j, x j * u j)) *
    PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure integralIndicator x =
    PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure integralIndicator x at h
  by_contra hn
  exact hphase ((mul_eq_right₀ hn).mp h)

theorem integralIndicator_fourier (x : ι → PoissonAutomorphyNormalizationData.AQf) :
    PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure integralIndicator x =
      (D.finiteMeasure.real (integralVectors (ι := ι) : Set (ι → PoissonAutomorphyNormalizationData.AQf)) : ℂ) * integralIndicator x := by
  by_cases hx : x ∈ integralVectors
  · rw [integralIndicator_fourier_of_mem D hx, integralIndicator_of_mem hx, mul_one]
  · rw [integralIndicator_fourier_of_notMem D hx, integralIndicator_of_notMem hx, mul_zero]

theorem integralVectors_volume : D.finiteMeasure.real (integralVectors (ι := ι) : Set (ι → PoissonAutomorphyNormalizationData.AQf)) = 1 := by
  let v := D.finiteMeasure.real (integralVectors (ι := ι) : Set (ι → PoissonAutomorphyNormalizationData.AQf))
  have h := D.finiteMeasure_selfDual integralTestFunction 0
  change PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure
    (PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure integralIndicator) 0 = integralIndicator (-0) at h
  rw [show PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure integralIndicator =
    (fun x => (v : ℂ) * integralIndicator x) from funext (integralIndicator_fourier D)] at h
  simp only [PoissonAutomorphyNormalizationData.fourier, mul_assoc, integral_const_mul] at h
  change (v : ℂ) * PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure integralIndicator 0 =
    integralIndicator (-0) at h
  rw [integralIndicator_fourier_of_mem D integralVectors.zero_mem,
    neg_zero, integralIndicator_of_mem integralVectors.zero_mem] at h
  have hv : v * v = 1 := by exact_mod_cast h
  have hv0 : 0 ≤ v := ENNReal.toReal_nonneg
  change v = 1
  nlinarith

theorem integralIndicator_selfFourier (x : ι → PoissonAutomorphyNormalizationData.AQf) :
    PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure integralIndicator x = integralIndicator x := by
  rw [integralIndicator_fourier, integralVectors_volume, Complex.ofReal_one, one_mul]

end

section

/-! A finite Schwartz function has a uniform integral lattice of translation periods. -/

open scoped Classical

variable {ι : Type*} [Fintype ι]

def translationStabilizer (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) : AddSubgroup (ι → PoissonAutomorphyNormalizationData.AQf) where
  carrier := {u | ∀ x, φ.val (u + x) = φ.val x}
  zero_mem' x := by rw [zero_add]
  add_mem' hu hv x := by rw [add_assoc, hu, hv]
  neg_mem' {u} hu x := by
    have h := hu (-u + x)
    rw [← add_assoc, add_neg_cancel, zero_add] at h
    exact h.symm

theorem translationStabilizer_isOpen (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    IsOpen (translationStabilizer φ : Set (ι → PoissonAutomorphyNormalizationData.AQf)) := by
  have hlc := (PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_mem_iff φ.val).mp φ.property |>.1
  let R : Set ((ι → PoissonAutomorphyNormalizationData.AQf) × (ι → PoissonAutomorphyNormalizationData.AQf)) := {p | φ.val (p.1 + p.2) - φ.val p.2 = 0}
  have hR : IsOpen R := by
    apply IsLocallyConstant.isOpen_fiber
    exact (hlc.comp_continuous (continuous_fst.add continuous_snd)).sub
      (hlc.comp_continuous continuous_snd)
  have hsub : ({0} : Set (ι → PoissonAutomorphyNormalizationData.AQf)) ×ˢ tsupport φ.val ⊆ R := by
    rintro ⟨u, x⟩ ⟨rfl, _⟩
    simp [R]
  obtain ⟨U, W, hU, _, hU0, hKW, hUW⟩ := generalized_tube_lemma
    isCompact_singleton (PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_hasCompactSupport φ) hR hsub
  have hsmall : U ∩ Neg.neg ⁻¹' U ⊆ (translationStabilizer φ : Set (ι → PoissonAutomorphyNormalizationData.AQf)) := by
    rintro u ⟨hu, hnu⟩ x
    by_cases hx : x ∈ tsupport φ.val
    · exact sub_eq_zero.mp (show φ.val (u + x) - φ.val x = 0 from
        hUW (show (u, x) ∈ U ×ˢ W from ⟨hu, hKW hx⟩))
    · by_cases hux : u + x ∈ tsupport φ.val
      · have h : φ.val (-u + (u + x)) = φ.val (u + x) := sub_eq_zero.mp
          (hUW (show (-u, u + x) ∈ U ×ˢ W from ⟨hnu, hKW hux⟩))
        rw [← add_assoc, neg_add_cancel, zero_add] at h
        exact h.symm
      · rw [image_eq_zero_of_notMem_tsupport hux, image_eq_zero_of_notMem_tsupport hx]
  apply (translationStabilizer φ).isOpen_of_mem_nhds (g := (0 : ι → PoissonAutomorphyNormalizationData.AQf))
  apply Filter.mem_of_superset ((hU.inter (hU.preimage continuous_neg)).mem_nhds ?_) hsmall
  exact ⟨hU0 rfl, by simpa only [Set.mem_preimage, neg_zero] using hU0 rfl⟩

instance integralVectorsCompact : CompactSpace (integralVectors (ι := ι)) :=
  isCompact_iff_compactSpace.mp integralVectors_isCompact

theorem finiteSchwartz_integral_period (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    ∃ n : ℕ, 0 < n ∧ ∀ (u : ι → PoissonAutomorphyNormalizationData.AQf), u ∈ integralVectors →
      ∀ x, φ.val (n • u + x) = φ.val x := by
  let H : AddSubgroup (integralVectors (ι := ι)) :=
    (translationStabilizer φ).comap integralVectors.toAddSubgroup.subtype
  have hH : IsOpen (H : Set (integralVectors (ι := ι))) :=
    (translationStabilizer_isOpen φ).preimage continuous_subtype_val
  let : Finite ((integralVectors (ι := ι)) ⧸ H) := H.quotient_finite_of_isOpen hH
  let n := Nat.card ((integralVectors (ι := ι)) ⧸ H)
  refine ⟨n, Nat.card_pos, ?_⟩
  intro u hu
  have h : n • (⟨u, hu⟩ : integralVectors) ∈ H := by
    apply (QuotientAddGroup.eq_zero_iff _).mp
    rw [QuotientAddGroup.mk_nsmul]
    exact card_nsmul_eq_zero'
  exact h

end

section

/-! Countability and measurable integration on the finite adeles. -/

open scoped Classical
open _root_.MeasureTheory

instance finitePlaceCountable : Countable AdelicSupport.PoissonAutomorphyConstruction.FinitePlace :=
  Countable.of_equiv Nat.Primes Rat.HeightOneSpectrum.primesEquiv.symm

instance integralAdeleSecondCountable : SecondCountableTopology AdelicSupport.PoissonAutomorphyConstruction.integralAdele :=
  integralPadicHomeomorph.symm.isEmbedding.secondCountableTopology

def rationalIntegralCover (x : Σ _q : ℚ, AdelicSupport.PoissonAutomorphyConstruction.integralAdele) : PoissonAutomorphyNormalizationData.AQf :=
  algebraMap ℚ PoissonAutomorphyNormalizationData.AQf x.1 + x.2.val

theorem rationalIntegralCover_isOpenQuotientMap : IsOpenQuotientMap rationalIntegralCover := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    obtain ⟨q, hq⟩ := finiteAdele_rational_representative a
    refine ⟨⟨q, ⟨a - algebraMap ℚ PoissonAutomorphyNormalizationData.AQf q, hq⟩⟩, ?_⟩
    dsimp [rationalIntegralCover]
    abel
  · apply continuous_sigma
    intro q
    change Continuous (fun a : AdelicSupport.PoissonAutomorphyConstruction.integralAdele => algebraMap ℚ PoissonAutomorphyNormalizationData.AQf q + a.val)
    exact continuous_const.add continuous_subtype_val
  · apply isOpenMap_sigma.mpr
    intro q
    exact (isOpenMap_add_left (algebraMap ℚ PoissonAutomorphyNormalizationData.AQf q)).comp
      AdelicSupport.PoissonAutomorphyConstruction.isOpen_integralAdele.isOpenEmbedding_subtypeVal.isOpenMap

instance finiteAdeleSecondCountable : SecondCountableTopology PoissonAutomorphyNormalizationData.AQf :=
  Topology.IsOpenQuotientMap.secondCountableTopology rationalIntegralCover_isOpenQuotientMap

variable {ι : Type*} [Fintype ι]

theorem finiteSchwartz_measurable (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) : Measurable φ.val :=
  (PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_continuous φ).measurable

theorem finiteSchwartz_integrable (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (μ : Measure (ι → PoissonAutomorphyNormalizationData.AQf))
    [μ.IsAddHaarMeasure] : Integrable φ.val μ := by
  exact (PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_continuous φ).integrable_of_hasCompactSupport
    (PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_hasCompactSupport φ)

end

section

/-! Rational scalings and compact open lattices in the finite adeles. -/

open scoped Classical
open _root_.MeasureTheory

variable {ι : Type*}

def finiteScale (q : ℚ) (x : ι → PoissonAutomorphyNormalizationData.AQf) : ι → PoissonAutomorphyNormalizationData.AQf :=
  fun i => algebraMap ℚ PoissonAutomorphyNormalizationData.AQf q * x i

theorem finiteScale_mul (p q : ℚ) (x : ι → PoissonAutomorphyNormalizationData.AQf) :
    finiteScale p (finiteScale q x) = finiteScale (p * q) x := by
  ext i
  simp only [finiteScale, map_mul, mul_assoc]

theorem finiteScale_one (x : ι → PoissonAutomorphyNormalizationData.AQf) : finiteScale 1 x = x := by
  ext i
  simp [finiteScale]

theorem finiteScale_add (q : ℚ) (x y : ι → PoissonAutomorphyNormalizationData.AQf) :
    finiteScale q (x + y) = finiteScale q x + finiteScale q y := by
  ext i
  simp [finiteScale, mul_add]

def finiteScaleEquiv (q : ℚ) (hq : q ≠ 0) : (ι → PoissonAutomorphyNormalizationData.AQf) ≃+ (ι → PoissonAutomorphyNormalizationData.AQf) where
  toFun := finiteScale q
  invFun := finiteScale q⁻¹
  left_inv x := by rw [finiteScale_mul, inv_mul_cancel₀ hq, finiteScale_one]
  right_inv x := by rw [finiteScale_mul, mul_inv_cancel₀ hq, finiteScale_one]
  map_add' := finiteScale_add q

theorem finiteScale_continuous (q : ℚ) : Continuous (finiteScale (ι := ι) q) := by
  apply continuous_pi
  intro i
  exact continuous_const.mul (continuous_apply i)

def finiteScaleHomeomorph (q : ℚ) (hq : q ≠ 0) : (ι → PoissonAutomorphyNormalizationData.AQf) ≃ₜ (ι → PoissonAutomorphyNormalizationData.AQf) where
  toEquiv := (finiteScaleEquiv q hq).toEquiv
  continuous_toFun := finiteScale_continuous q
  continuous_invFun := finiteScale_continuous q⁻¹

def finiteLattice (q : ℚ) (hq : q ≠ 0) : AddSubgroup (ι → PoissonAutomorphyNormalizationData.AQf) :=
  integralVectors.toAddSubgroup.map (finiteScaleEquiv q hq).toAddMonoidHom

theorem finiteLattice_coe (q : ℚ) (hq : q ≠ 0) :
    (finiteLattice (ι := ι) q hq : Set (ι → PoissonAutomorphyNormalizationData.AQf)) =
      finiteScale q '' (integralVectors (ι := ι) : Set (ι → PoissonAutomorphyNormalizationData.AQf)) := rfl

theorem finiteLattice_mem_iff (q : ℚ) (hq : q ≠ 0) (x : ι → PoissonAutomorphyNormalizationData.AQf) :
    x ∈ finiteLattice q hq ↔ finiteScale q⁻¹ x ∈ integralVectors := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    change finiteScale q⁻¹ (finiteScale q u) ∈ integralVectors
    rw [finiteScale_mul, inv_mul_cancel₀ hq, finiteScale_one]
    exact hu
  · intro hx
    refine ⟨finiteScale q⁻¹ x, hx, ?_⟩
    exact (finiteScaleEquiv q hq).apply_symm_apply x

theorem finiteLattice_isCompact (q : ℚ) (hq : q ≠ 0) :
    IsCompact (finiteLattice (ι := ι) q hq : Set (ι → PoissonAutomorphyNormalizationData.AQf)) := by
  rw [finiteLattice_coe]
  exact integralVectors_isCompact.image (finiteScale_continuous q)

variable [Fintype ι]

theorem finiteLattice_isOpen (q : ℚ) (hq : q ≠ 0) :
    IsOpen (finiteLattice (ι := ι) q hq : Set (ι → PoissonAutomorphyNormalizationData.AQf)) := by
  rw [finiteLattice_coe]
  exact (finiteScaleHomeomorph q hq).isOpenMap _ integralVectors_isOpen

theorem finiteLattice_measurableSet (q : ℚ) (hq : q ≠ 0) :
    MeasurableSet (finiteLattice (ι := ι) q hq : Set (ι → PoissonAutomorphyNormalizationData.AQf)) :=
  (finiteLattice_isOpen q hq).measurableSet

omit [Fintype ι] in
theorem finiteScale_natCast (n : ℕ) (x : ι → PoissonAutomorphyNormalizationData.AQf) : finiteScale (n : ℚ) x = n • x := by
  ext i
  simp [finiteScale, nsmul_eq_mul]

theorem finiteSchwartz_lattice_period (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    ∃ n : ℕ, ∃ hn : 0 < n, ∀ u ∈ finiteLattice (n : ℚ) (by exact_mod_cast hn.ne'),
      ∀ x, φ.val (u + x) = φ.val x := by
  obtain ⟨n, hn, hperiod⟩ := finiteSchwartz_integral_period φ
  refine ⟨n, hn, ?_⟩
  rintro u ⟨v, hv, rfl⟩ x
  change φ.val (finiteScale (n : ℚ) v + x) = φ.val x
  rw [finiteScale_natCast]
  exact hperiod v hv x

end

section

/-! Finite residue representatives for integral finite lattices. -/

open scoped Classical

variable {ι : Type*}

def integerFinite (m : ι → ℤ) : ι → PoissonAutomorphyNormalizationData.AQf := fun i => (m i : PoissonAutomorphyNormalizationData.AQf)

def integralVectorHomeomorph : (ι → AdelicSupport.PoissonAutomorphyConstruction.integralAdele) ≃ₜ integralVectors (ι := ι) where
  toFun x := ⟨fun i => (x i).val, fun i => (x i).property⟩
  invFun x i := ⟨x.val i, x.property i⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)).subtype_mk _
  continuous_invFun := continuous_pi fun i =>
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _

def integralIntegerMap (m : ι → ℤ) : integralVectors (ι := ι) :=
  ⟨integerFinite m, fun i => intCast_mem AdelicSupport.PoissonAutomorphyConstruction.integralAdele (m i)⟩

theorem denseRange_integralIntegerMap : DenseRange (integralIntegerMap (ι := ι)) := by
  have h := integralVectorHomeomorph.surjective.denseRange.comp
    (DenseRange.piMap (fun _ : ι => denseRange_integer_integralAdele))
    integralVectorHomeomorph.continuous
  exact h

variable [Fintype ι]

theorem integralVector_integer_coset (n : ℕ) (hn : 0 < n)
    (u : ι → PoissonAutomorphyNormalizationData.AQf) (hu : u ∈ integralVectors) :
    ∃ m : ι → ℤ, u - integerFinite m ∈ finiteLattice (n : ℚ) (by exact_mod_cast hn.ne') := by
  let hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hopen : IsOpen {a : integralVectors (ι := ι) | u - a.val ∈ finiteLattice (n : ℚ) hnq} :=
    (finiteLattice_isOpen (n : ℚ) hnq).preimage (continuous_const.sub continuous_subtype_val)
  obtain ⟨m, hm⟩ := denseRange_integralIntegerMap.exists_mem_open hopen
    ⟨⟨u, hu⟩, by simp⟩
  exact ⟨m, hm⟩

omit [Fintype ι] in
theorem integerFinite_mem_finiteLattice_iff (n : ℕ) (hn : 0 < n) (m : ι → ℤ) :
    integerFinite m ∈ finiteLattice (n : ℚ) (by exact_mod_cast hn.ne') ↔
      ∀ i, (n : ℤ) ∣ m i := by
  rw [finiteLattice_mem_iff]
  change (∀ i, algebraMap ℚ PoissonAutomorphyNormalizationData.AQf ((n : ℚ)⁻¹) * (m i : PoissonAutomorphyNormalizationData.AQf) ∈ AdelicSupport.PoissonAutomorphyConstruction.integralAdele) ↔ _
  simp only [← map_intCast (algebraMap ℚ PoissonAutomorphyNormalizationData.AQf), ← map_mul, AdelicSupport.PoissonAutomorphyConstruction.rational_integral_iff]
  apply forall_congr'
  intro i
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have h : (m i : ℚ) = (n : ℚ) * (k : ℚ) := by rw [hk, ← mul_assoc, mul_inv_cancel₀ hnq, one_mul]
    exact_mod_cast h
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [hk, Int.cast_mul, Int.cast_natCast, ← mul_assoc, inv_mul_cancel₀ hnq, one_mul]

def residuePoint {n : ℕ} (r : ι → ZMod n) : ι → PoissonAutomorphyNormalizationData.AQf :=
  integerFinite (fun i => (r i).val)

theorem integralVector_residue_coset (n : ℕ) (hn : 0 < n)
    (u : ι → PoissonAutomorphyNormalizationData.AQf) (hu : u ∈ integralVectors) :
    ∃ r : ι → ZMod n, u - residuePoint r ∈ finiteLattice (n : ℚ) (by exact_mod_cast hn.ne') := by
  let : NeZero n := ⟨hn.ne'⟩
  obtain ⟨m, hm⟩ := integralVector_integer_coset n hn u hu
  let r : ι → ZMod n := fun i => (m i : ZMod n)
  refine ⟨r, ?_⟩
  have hr : integerFinite m - residuePoint r ∈ finiteLattice (n : ℚ) (by exact_mod_cast hn.ne') := by
    have hfun : integerFinite m - residuePoint r =
        integerFinite (fun i => m i - ((r i).val : ℤ)) := by
      ext i
      simp [integerFinite, residuePoint]
    rw [hfun, integerFinite_mem_finiteLattice_iff n hn]
    intro i
    apply (ZMod.intCast_eq_intCast_iff_dvd_sub ((r i).val : ℤ) (m i) n).mp
    simp [r]
  simpa only [sub_add_sub_cancel] using (finiteLattice (n : ℚ) (by exact_mod_cast hn.ne')).add_mem hm hr

omit [Fintype ι] in
theorem residue_cosets_disjoint (n : ℕ) (hn : 0 < n) :
    Pairwise (fun r s : ι → ZMod n => Disjoint
      {x : ι → PoissonAutomorphyNormalizationData.AQf | x - residuePoint r ∈ finiteLattice (n : ℚ) (by exact_mod_cast hn.ne')}
      {x : ι → PoissonAutomorphyNormalizationData.AQf | x - residuePoint s ∈ finiteLattice (n : ℚ) (by exact_mod_cast hn.ne')}) := by
  let : NeZero n := ⟨hn.ne'⟩
  intro r s hrs
  apply Set.disjoint_left.mpr
  intro x hxr hxs
  apply hrs
  have h := (finiteLattice (n : ℚ) (by exact_mod_cast hn.ne')).sub_mem hxr hxs
  have heq : (x - residuePoint r) - (x - residuePoint s) =
      integerFinite (fun i => ((s i).val : ℤ) - ((r i).val : ℤ)) := by
    ext i
    simp only [Pi.sub_apply, integerFinite, residuePoint, Int.cast_sub, Int.cast_natCast]
    ring_nf
  rw [heq, integerFinite_mem_finiteLattice_iff n hn] at h
  funext i
  have hi := (ZMod.intCast_eq_intCast_iff_dvd_sub ((r i).val : ℤ) ((s i).val : ℤ) n).mpr (h i)
  simpa only [Int.cast_natCast, ZMod.natCast_zmod_val] using hi

end

section

/-! Exact Haar volumes of integral finite sublattices. -/

open scoped Classical ENNReal
open _root_.MeasureTheory

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem finiteLattice_nat_subset_integral (n : ℕ) (hn : 0 < n) :
    finiteLattice (ι := ι) (n : ℚ) (by exact_mod_cast hn.ne') ≤ integralVectors.toAddSubgroup := by
  rintro x ⟨u, hu, rfl⟩ i
  change algebraMap ℚ PoissonAutomorphyNormalizationData.AQf (n : ℚ) * u i ∈ AdelicSupport.PoissonAutomorphyConstruction.integralAdele
  exact AdelicSupport.PoissonAutomorphyConstruction.integralAdele.mul_mem (by simpa only [map_natCast] using natCast_mem AdelicSupport.PoissonAutomorphyConstruction.integralAdele n) (hu i)

theorem integralVectors_residue_partition (n : ℕ) (hn : 0 < n) :
    (integralVectors (ι := ι) : Set (ι → PoissonAutomorphyNormalizationData.AQf)) =
      ⋃ r : ι → ZMod n, {x | x - residuePoint r ∈ finiteLattice (n : ℚ) (by exact_mod_cast hn.ne')} := by
  ext x
  constructor
  · intro hx
    obtain ⟨r, hr⟩ := integralVector_residue_coset n hn x hx
    exact Set.mem_iUnion.mpr ⟨r, hr⟩
  · intro hx
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp hx
    have h := integralVectors.add_mem (finiteLattice_nat_subset_integral n hn hr)
      (integralIntegerMap (fun i => ((r i).val : ℤ))).property
    simpa only [residuePoint, integralIntegerMap, sub_add_cancel, SetLike.mem_coe] using h

variable [DecidableEq ι] {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

theorem finiteLattice_nat_volume (n : ℕ) (hn : 0 < n) :
    D.finiteMeasure.real (finiteLattice (ι := ι) (n : ℚ) (by exact_mod_cast hn.ne') : Set (ι → PoissonAutomorphyNormalizationData.AQf)) =
      ((n : ℝ) ^ Fintype.card ι)⁻¹ := by
  let := D.finiteMeasure_haar
  let : NeZero n := ⟨hn.ne'⟩
  let L := finiteLattice (ι := ι) (n : ℚ) (by exact_mod_cast hn.ne')
  have hcoset (r : ι → ZMod n) : D.finiteMeasure {x : ι → PoissonAutomorphyNormalizationData.AQf | x - residuePoint r ∈ L} =
      D.finiteMeasure (L : Set (ι → PoissonAutomorphyNormalizationData.AQf)) := by
    simpa only [sub_eq_add_neg, Set.preimage, SetLike.mem_coe] using
      measure_preimage_add_right D.finiteMeasure (-residuePoint r) (L : Set (ι → PoissonAutomorphyNormalizationData.AQf))
  have hmeasure : D.finiteMeasure (integralVectors (ι := ι) : Set (ι → PoissonAutomorphyNormalizationData.AQf)) =
      (n : ℝ≥0∞) ^ Fintype.card ι * D.finiteMeasure (L : Set (ι → PoissonAutomorphyNormalizationData.AQf)) := by
    rw [integralVectors_residue_partition n hn]
    rw [measure_iUnion (residue_cosets_disjoint n hn)
      (fun r => (finiteLattice_measurableSet (n : ℚ) (by exact_mod_cast hn.ne')).preimage
        (measurable_id.sub measurable_const))]
    change (∑' r : ι → ZMod n, D.finiteMeasure {x : ι → PoissonAutomorphyNormalizationData.AQf | x - residuePoint r ∈ L}) = _
    simp only [hcoset, tsum_fintype, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, ZMod.card, nsmul_eq_mul, Nat.cast_pow]
  have hreal := congrArg ENNReal.toReal hmeasure
  change D.finiteMeasure.real (integralVectors (ι := ι) : Set (ι → PoissonAutomorphyNormalizationData.AQf)) = _ at hreal
  rw [integralVectors_volume D] at hreal
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] at hreal
  have hnreal : (n : ℝ) ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (by exact_mod_cast hn.ne')
  apply (mul_left_cancel₀ hnreal)
  rw [mul_inv_cancel₀ hnreal]
  exact hreal.symm

end

section

/-! Finite Fourier transforms of scaled integral-lattice indicators. -/

open scoped Classical
open _root_.MeasureTheory

variable {ι : Type*}

def latticeIndicator (q : ℚ) (hq : q ≠ 0) (x : ι → PoissonAutomorphyNormalizationData.AQf) : ℂ :=
  (finiteLattice (ι := ι) q hq : Set (ι → PoissonAutomorphyNormalizationData.AQf)).indicator (fun _ => 1) x

theorem latticeIndicator_of_mem (q : ℚ) (hq : q ≠ 0) {x : ι → PoissonAutomorphyNormalizationData.AQf}
    (hx : x ∈ finiteLattice q hq) : latticeIndicator q hq x = 1 := Set.indicator_of_mem hx _

theorem latticeIndicator_of_notMem (q : ℚ) (hq : q ≠ 0) {x : ι → PoissonAutomorphyNormalizationData.AQf}
    (hx : x ∉ finiteLattice q hq) : latticeIndicator q hq x = 0 := Set.indicator_of_notMem hx _

theorem latticeIndicator_add (q : ℚ) (hq : q ≠ 0) {u : ι → PoissonAutomorphyNormalizationData.AQf}
    (hu : u ∈ finiteLattice q hq) (y : ι → PoissonAutomorphyNormalizationData.AQf) :
    latticeIndicator q hq (u + y) = latticeIndicator q hq y := by
  have hmem : u + y ∈ finiteLattice q hq ↔ y ∈ finiteLattice q hq := by
    constructor
    · intro h
      simpa only [add_sub_cancel_left] using (finiteLattice q hq).sub_mem h hu
    · exact (finiteLattice q hq).add_mem hu
  simp only [latticeIndicator, Set.indicator, SetLike.mem_coe, hmem]

variable [Fintype ι] [DecidableEq ι] {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]
  (D : PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA)

theorem finiteCharacter_pairing_dual_lattice (q : ℚ) (hq : q ≠ 0)
    {x y : ι → PoissonAutomorphyNormalizationData.AQf} (hx : x ∈ finiteLattice q⁻¹ (inv_ne_zero hq))
    (hy : y ∈ finiteLattice q hq) : D.finiteCharacter (-(∑ i, x i * y i)) = 1 := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  change D.finiteCharacter (-(∑ i, finiteScale q⁻¹ u i * finiteScale q v i)) = 1
  have heq (i : ι) : finiteScale q⁻¹ u i * finiteScale q v i = u i * v i := by
    dsimp [finiteScale]
    calc
      _ = (algebraMap ℚ PoissonAutomorphyNormalizationData.AQf q⁻¹ * algebraMap ℚ PoissonAutomorphyNormalizationData.AQf q) * (u i * v i) := by ring
      _ = _ := by rw [← map_mul, inv_mul_cancel₀ hq, map_one, one_mul]
  simp only [heq]
  exact finiteCharacter_pairing_integral D hu hv

theorem latticeIndicator_fourier_of_mem (q : ℚ) (hq : q ≠ 0) {x : ι → PoissonAutomorphyNormalizationData.AQf}
    (hx : x ∈ finiteLattice q⁻¹ (inv_ne_zero hq)) :
    PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure (latticeIndicator q hq) x =
      (D.finiteMeasure.real (finiteLattice (ι := ι) q hq : Set (ι → PoissonAutomorphyNormalizationData.AQf)) : ℂ) := by
  have heq : (fun y => latticeIndicator q hq y * D.finiteCharacter (-(∑ i, x i * y i))) =
      latticeIndicator q hq := by
    funext y
    by_cases hy : y ∈ finiteLattice q hq
    · rw [latticeIndicator_of_mem q hq hy, finiteCharacter_pairing_dual_lattice D q hq hx hy, one_mul]
    · rw [latticeIndicator_of_notMem q hq hy, zero_mul]
  rw [PoissonAutomorphyNormalizationData.fourier, heq]
  change (∫ y, (finiteLattice (ι := ι) q hq : Set (ι → PoissonAutomorphyNormalizationData.AQf)).indicator
    (fun _ => (1 : ℂ)) y ∂D.finiteMeasure) = _
  rw [integral_indicator (finiteLattice_measurableSet q hq)]
  simp

theorem latticeIndicator_fourier_of_notMem (q : ℚ) (hq : q ≠ 0) {x : ι → PoissonAutomorphyNormalizationData.AQf}
    (hx : x ∉ finiteLattice q⁻¹ (inv_ne_zero hq)) :
    PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure (latticeIndicator q hq) x = 0 := by
  let := D.finiteMeasure_haar
  have hx' : finiteScale q x ∉ integralVectors := by
    simpa only [finiteLattice_mem_iff, inv_inv] using hx
  obtain ⟨i, hi⟩ : ∃ i, algebraMap ℚ PoissonAutomorphyNormalizationData.AQf q * x i ∉ AdelicSupport.PoissonAutomorphyConstruction.integralAdele := not_forall.mp hx'
  let v : ι → PoissonAutomorphyNormalizationData.AQf := Pi.single i 1
  let u := finiteScale q v
  have hu : u ∈ finiteLattice q hq := by
    refine ⟨v, ?_, rfl⟩
    intro j
    by_cases hj : j = i <;> simp [v, hj, AdelicSupport.PoissonAutomorphyConstruction.integralAdele.one_mem, AdelicSupport.PoissonAutomorphyConstruction.integralAdele.zero_mem]
  have hpair : (∑ j, x j * u j) = algebraMap ℚ PoissonAutomorphyNormalizationData.AQf q * x i := by
    calc
      _ = algebraMap ℚ PoissonAutomorphyNormalizationData.AQf q * (∑ j, x j * v j) := by
        simp only [u, finiteScale, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [show (∑ j, x j * v j) = x i from dotProduct_single_one x i]
  have hphase : D.finiteCharacter (-(∑ j, x j * u j)) ≠ 1 := by
    rw [hpair]
    intro h
    exact hi (AdelicSupport.PoissonAutomorphyConstruction.integralAdele.neg_mem_iff.mp ((finiteCharacter_eq_one_iff D _).mp h))
  let F := fun y : ι → PoissonAutomorphyNormalizationData.AQf => latticeIndicator q hq y * D.finiteCharacter (-(∑ j, x j * y j))
  have hshift (y : ι → PoissonAutomorphyNormalizationData.AQf) : F (u + y) = D.finiteCharacter (-(∑ j, x j * u j)) * F y := by
    dsimp [F]
    rw [latticeIndicator_add q hq hu]
    simp only [mul_add, Finset.sum_add_distrib, neg_add, AddChar.map_add_eq_mul]
    ring
  have h := integral_add_left_eq_self (μ := D.finiteMeasure) F u
  simp_rw [hshift, integral_const_mul] at h
  change D.finiteCharacter (-(∑ j, x j * u j)) *
    PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure (latticeIndicator q hq) x =
    PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure (latticeIndicator q hq) x at h
  by_contra hn
  exact hphase ((mul_eq_right₀ hn).mp h)

theorem latticeIndicator_fourier (q : ℚ) (hq : q ≠ 0) (x : ι → PoissonAutomorphyNormalizationData.AQf) :
    PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure (latticeIndicator q hq) x =
      (D.finiteMeasure.real (finiteLattice (ι := ι) q hq : Set (ι → PoissonAutomorphyNormalizationData.AQf)) : ℂ) *
        latticeIndicator q⁻¹ (inv_ne_zero hq) x := by
  by_cases hx : x ∈ finiteLattice q⁻¹ (inv_ne_zero hq)
  · rw [latticeIndicator_fourier_of_mem D q hq hx,
      latticeIndicator_of_mem q⁻¹ (inv_ne_zero hq) hx, mul_one]
  · rw [latticeIndicator_fourier_of_notMem D q hq hx,
      latticeIndicator_of_notMem q⁻¹ (inv_ne_zero hq) hx, mul_zero]

def latticeCosetIndicator (q : ℚ) (hq : q ≠ 0) (a x : ι → PoissonAutomorphyNormalizationData.AQf) : ℂ :=
  latticeIndicator q hq (x - a)

theorem latticeCosetIndicator_fourier (q : ℚ) (hq : q ≠ 0) (a x : ι → PoissonAutomorphyNormalizationData.AQf) :
    PoissonAutomorphyNormalizationData.fourier D.finiteCharacter D.finiteMeasure (latticeCosetIndicator q hq a) x =
      D.finiteCharacter (-(∑ i, x i * a i)) *
        ((D.finiteMeasure.real (finiteLattice (ι := ι) q hq : Set (ι → PoissonAutomorphyNormalizationData.AQf)) : ℂ) *
          latticeIndicator q⁻¹ (inv_ne_zero hq) x) := by
  let := D.finiteMeasure_haar
  rw [← latticeIndicator_fourier D q hq x]
  change (∫ y, latticeCosetIndicator q hq a y * D.finiteCharacter (-(∑ i, x i * y i))
    ∂D.finiteMeasure) = _
  rw [← integral_add_right_eq_self (μ := D.finiteMeasure)
    (fun y => latticeCosetIndicator q hq a y * D.finiteCharacter (-(∑ i, x i * y i))) a]
  calc
    _ = ∫ y, D.finiteCharacter (-(∑ i, x i * a i)) *
        (latticeIndicator q hq y * D.finiteCharacter (-(∑ i, x i * y i))) ∂D.finiteMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        dsimp only [latticeCosetIndicator]
        rw [add_sub_cancel_right]
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, neg_add, AddChar.map_add_eq_mul]
        ring
    _ = _ := integral_const_mul _ _

end

/-! Finite Schwartz functions are finite sums of rational lattice cosets. -/

open scoped Classical

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
theorem denseRange_finiteDiagonal : DenseRange (PoissonAutomorphyNormalizationData.finiteDiagonal (ι := ι)) :=
  DenseRange.piMap (fun _ : ι => denseRange_rational_finiteAdele)

theorem finiteLattice_rational_coset (q : ℚ) (hq : q ≠ 0) (x : ι → PoissonAutomorphyNormalizationData.AQf) :
    ∃ a : ι → ℚ, x - PoissonAutomorphyNormalizationData.finiteDiagonal a ∈ finiteLattice q hq := by
  exact denseRange_finiteDiagonal.exists_mem_open
    (s := {y : ι → PoissonAutomorphyNormalizationData.AQf | x - y ∈ finiteLattice q hq})
    ((finiteLattice_isOpen q hq).preimage (continuous_const.sub continuous_id))
    ⟨x, by simp⟩

abbrev FiniteQuotient (q : ℚ) (hq : q ≠ 0) := (ι → PoissonAutomorphyNormalizationData.AQf) ⧸ finiteLattice q hq

def rationalQuotientMap (q : ℚ) (hq : q ≠ 0) (a : ι → ℚ) : FiniteQuotient (ι := ι) q hq :=
  QuotientAddGroup.mk (PoissonAutomorphyNormalizationData.finiteDiagonal a)

theorem rationalQuotientMap_surjective (q : ℚ) (hq : q ≠ 0) :
    Function.Surjective (rationalQuotientMap (ι := ι) q hq) := by
  intro c
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective c
  obtain ⟨a, ha⟩ := finiteLattice_rational_coset q hq x
  refine ⟨a, ?_⟩
  symm
  exact QuotientAddGroup.eq_iff_sub_mem.mpr ha

def finiteQuotientRep (q : ℚ) (hq : q ≠ 0) (c : FiniteQuotient (ι := ι) q hq) : ι → ℚ :=
  (rationalQuotientMap_surjective q hq c).choose

theorem finiteQuotientRep_covers (q : ℚ) (hq : q ≠ 0) (c : FiniteQuotient (ι := ι) q hq) :
    (QuotientAddGroup.mk (PoissonAutomorphyNormalizationData.finiteDiagonal (finiteQuotientRep q hq c)) : FiniteQuotient q hq) = c :=
  (rationalQuotientMap_surjective q hq c).choose_spec

theorem cosetIndicator_quotient (q : ℚ) (hq : q ≠ 0)
    (c : FiniteQuotient (ι := ι) q hq) (x : ι → PoissonAutomorphyNormalizationData.AQf) :
    latticeCosetIndicator q hq (PoissonAutomorphyNormalizationData.finiteDiagonal (finiteQuotientRep q hq c)) x =
      if (QuotientAddGroup.mk x : FiniteQuotient q hq) = c then 1 else 0 := by
  have hmem : x - PoissonAutomorphyNormalizationData.finiteDiagonal (finiteQuotientRep q hq c) ∈ finiteLattice q hq ↔
      (QuotientAddGroup.mk x : FiniteQuotient q hq) = c := by
    rw [← QuotientAddGroup.eq_iff_sub_mem, finiteQuotientRep_covers]
  simp only [latticeCosetIndicator, latticeIndicator, Set.indicator, SetLike.mem_coe, hmem]

theorem finiteSchwartz_coset_expansion (φ : PoissonAutomorphyNormalizationData.finiteSchwartz ι) (q : ℚ) (hq : q ≠ 0)
    (hp : ∀ u ∈ finiteLattice q hq, ∀ x, φ.val (u + x) = φ.val x) :
    ∃ s : Finset (FiniteQuotient (ι := ι) q hq), ∀ x : ι → PoissonAutomorphyNormalizationData.AQf,
      φ.val x = ∑ c ∈ s, φ.val (PoissonAutomorphyNormalizationData.finiteDiagonal (finiteQuotientRep q hq c)) *
        latticeCosetIndicator q hq (PoissonAutomorphyNormalizationData.finiteDiagonal (finiteQuotientRep q hq c)) x := by
  let : DiscreteTopology (FiniteQuotient (ι := ι) q hq) :=
    QuotientAddGroup.discreteTopology (finiteLattice_isOpen q hq)
  let Q : (ι → PoissonAutomorphyNormalizationData.AQf) → FiniteQuotient q hq := QuotientAddGroup.mk
  have hcompact := (PoissonAutomorphyNormalizationData.Construction.finiteSchwartz_hasCompactSupport φ).image
    (QuotientAddGroup.continuous_mk : Continuous Q)
  let s := hcompact.finite_of_discrete.toFinset
  have hcoeff (x : ι → PoissonAutomorphyNormalizationData.AQf) : φ.val (PoissonAutomorphyNormalizationData.finiteDiagonal (finiteQuotientRep q hq (Q x))) = φ.val x := by
    have hdiff : PoissonAutomorphyNormalizationData.finiteDiagonal (finiteQuotientRep q hq (Q x)) - x ∈ finiteLattice q hq :=
      QuotientAddGroup.eq_iff_sub_mem.mp (finiteQuotientRep_covers q hq (Q x))
    simpa only [sub_add_cancel] using hp _ hdiff x
  refine ⟨s, fun x => ?_⟩
  symm
  rw [Finset.sum_eq_single (Q x)]
  · rw [cosetIndicator_quotient, ite_eq_left rfl, mul_one, hcoeff]
  · intro c _ hc
    rw [cosetIndicator_quotient, ite_eq_right (Ne.symm hc), mul_zero]
  · intro hx
    rw [cosetIndicator_quotient, ite_eq_left rfl, mul_one, hcoeff]
    by_contra hφ
    apply hx
    apply (hcompact.finite_of_discrete.mem_toFinset).mpr
    exact ⟨x, subset_tsupport φ.val hφ, rfl⟩

end

end OAI.RepresentationTheory.Theta.PoissonAutomorphyFiniteFourier.Construction
