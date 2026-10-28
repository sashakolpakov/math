import Mathlib

/-! # Period Ring -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.PeriodInvariants.PeriodRing

/-!
# Concrete period-ring foundations for PeriodInvariants

The coefficient ring in this file is the actual valuation ring of `ℂ_p`.
Its completeness and the domain property of its tilt are proved here, rather
than included as assumptions of a comparison interface.

The divided-power completion and cyclotomic logarithm follow the construction
in Brinon--Conrad, *CMI notes on p-adic Hodge theory*, §9.1:
https://math.stanford.edu/~conrad/papers/notes.pdf

The definitions below do not yet establish nontriviality of `Bcris`, its fixed
scalars, an action of `G_K` on `Bcris`, or the geometric comparison theorem.
-/

open Valuation _root_.Topology Filter
open scoped NNReal

variable (p : ℕ) [hp : Fact p.Prime]

theorem complex_valuation_norm (x : ℂ_[p]) :
    ((Valued.v x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [PadicComplex.norm_eq_norm, Valuation.norm_def,
    PadicComplex.RankOne.hom_eq_embedding, embedding_restrict]

instance complexInt_complete : CompleteSpace 𝓞_ℂ_[p] :=
  (Valued.isClosed_valuationSubring ℂ_[p]).completeSpace_coe

theorem complexInt_norm_p : ‖(p : 𝓞_ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  change ‖(p : ℂ_[p])‖ = _
  rw [← complex_valuation_norm, PadicComplex.valuation_p]
  simp

theorem complexInt_norm_p_pos : 0 < ‖(p : 𝓞_ℂ_[p])‖ := by
  rw [complexInt_norm_p]
  exact inv_pos.mpr (by exact_mod_cast hp.out.pos)

theorem complexInt_norm_p_lt_one : ‖(p : 𝓞_ℂ_[p])‖ < 1 := by
  rw [complexInt_norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

instance complexInt_p_not_unit : Fact (¬ IsUnit (p : 𝓞_ℂ_[p])) := by
  constructor
  rw [(PadicComplexInt.integers p).isUnit_iff_valuation_eq_one]
  change ¬ Valued.v (p : ℂ_[p]) = 1
  simp [PadicComplex.valuation_p, hp.out.ne_one]

theorem complexInt_span_closedBall (x : 𝓞_ℂ_[p]) :
    (Ideal.span {x} : Set 𝓞_ℂ_[p]) = Metric.closedBall 0 ‖x‖ := by
  rw [(PadicComplexInt.integers p).coe_span_singleton_eq_setOfPred_le_v_algebraMap]
  ext y
  change Valued.v (y : ℂ_[p]) ≤ Valued.v (x : ℂ_[p]) ↔ _
  rw [← NNReal.coe_le_coe, complex_valuation_norm, complex_valuation_norm]
  simp [Metric.mem_closedBall, dist_zero_right]

theorem complexInt_p_adic : IsAdic (Ideal.span {(p : 𝓞_ℂ_[p])}) := by
  have hballs (n : ℕ) :
      (((Ideal.span {(p : 𝓞_ℂ_[p])}) ^ n : Ideal 𝓞_ℂ_[p]) : Set 𝓞_ℂ_[p]) =
        Metric.closedBall 0 (‖(p : 𝓞_ℂ_[p])‖ ^ n) := by
    rw [Ideal.span_singleton_pow, complexInt_span_closedBall]
    exact congrArg (Metric.closedBall (0 : 𝓞_ℂ_[p])) (norm_pow _ n)
  rw [isAdic_iff]
  constructor
  · intro n
    rw [hballs]
    exact IsUltrametricDist.isOpen_closedBall 0
      (pow_ne_zero n (ne_of_gt (complexInt_norm_p_pos p)))
  · intro s hs
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (complexInt_norm_p_lt_one p)
    refine ⟨n, ?_⟩
    rw [hballs]
    exact (Metric.closedBall_subset_ball hn).trans hball

instance complexInt_p_complete :
    IsAdicComplete (Ideal.span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] :=
  (complexInt_p_adic p).isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

theorem complex_mem_integer_of_pow {z : ℂ_[p]} (x : 𝓞_ℂ_[p])
    (hz : z ^ p = (x : ℂ_[p])) : z ∈ 𝓞_ℂ_[p] := by
  change Valued.v z ≤ 1
  apply (pow_le_one_iff_of_nonneg (show 0 ≤ (Valued.v z : ℝ≥0) from bot_le)
    hp.out.ne_zero).mp
  rw [← map_pow, hz]
  exact x.property

/-- Algebraic closedness of `ℂ_p` supplies integral `p`th roots of integral
elements; the valuation bound is proved, not assumed. -/
theorem complexInt_pow_surjective :
    Function.Surjective (fun x : 𝓞_ℂ_[p] => x ^ p) := by
  intro x
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ_[p]) hp.out.pos
  refine ⟨⟨z, complex_mem_integer_of_pow p x hz⟩, ?_⟩
  exact Subtype.ext hz

theorem modP_frobenius_surjective :
    Function.Surjective (frobenius (ModP 𝓞_ℂ_[p] p) p) := by
  intro q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨y, hy⟩ := complexInt_pow_surjective p x
  change y ^ p = x at hy
  refine ⟨Ideal.Quotient.mk _ y, ?_⟩
  change (Ideal.Quotient.mk _ y) ^ p = Ideal.Quotient.mk _ x
  rw [← map_pow, hy]

/-- Fontaine's actual integral period ring before adjoining divided powers. -/
abbrev Ainf := WittVector p (PreTilt 𝓞_ℂ_[p] p)

/-- Fontaine's theta map, using the proved completeness of `𝓞_ℂ_p`. -/
def theta : Ainf p →+* 𝓞_ℂ_[p] := WittVector.fontaineTheta 𝓞_ℂ_[p] p

theorem theta_surjective : Function.Surjective (theta p) :=
  surjective_fontaineTheta (modP_frobenius_surjective p)

instance complexInt_tilt_domain : IsDomain (PreTilt 𝓞_ℂ_[p] p) :=
  PreTilt.isDomain ℂ_[p] Valued.v 𝓞_ℂ_[p] (PadicComplexInt.integers p) p

instance ainf_domain : IsDomain (Ainf p) := inferInstance

instance ainf_charZero : CharZero (Ainf p) where
  cast_injective m n h := by
    apply Nat.cast_injective (R := 𝓞_ℂ_[p])
    simpa only [map_natCast] using congrArg (theta p) h

@[simp]
theorem theta_teichmuller (x : PreTilt 𝓞_ℂ_[p] p) :
    theta p (WittVector.teichmuller p x) = x.untilt :=
  WittVector.fontaineTheta_teichmuller x

/-- The divided-power generators inside the fraction field of `A_inf`.
This ambient field allows the factorial denominators to be written directly. -/
def dividedPowerGenerators : Set (FractionRing (Ainf p)) :=
  Set.range fun z : ℕ × RingHom.ker (theta p) =>
    (algebraMap (Ainf p) (FractionRing (Ainf p)) (z.2 : Ainf p)) ^ z.1 /
      (z.1.factorial : FractionRing (Ainf p))

/-- The concrete uncompleted divided-power envelope generated by
`x^n/n!` for `x ∈ ker θ`. -/
def acrisZeroSubalgebra : Subalgebra (Ainf p) (FractionRing (Ainf p)) :=
  Algebra.adjoin (Ainf p) (dividedPowerGenerators p)

abbrev AcrisZero : Type := acrisZeroSubalgebra p

/-- An individual divided power, as an element of the integral envelope. -/
def dividedPower (n : ℕ) (x : RingHom.ker (theta p)) : AcrisZero p :=
  ⟨(algebraMap (Ainf p) (FractionRing (Ainf p)) (x : Ainf p)) ^ n /
      (n.factorial : FractionRing (Ainf p)),
    Algebra.subset_adjoin ⟨(n, x), rfl⟩⟩

@[simp]
theorem dividedPower_coe (n : ℕ) (x : RingHom.ker (theta p)) :
    (dividedPower p n x : FractionRing (Ainf p)) =
      (algebraMap (Ainf p) (FractionRing (Ainf p)) (x : Ainf p)) ^ n /
        (n.factorial : FractionRing (Ainf p)) := rfl

@[simp]
theorem dividedPower_zero (x : RingHom.ker (theta p)) : dividedPower p 0 x = 1 := by
  apply Subtype.ext
  simp

@[simp]
theorem dividedPower_one (x : RingHom.ker (theta p)) :
    dividedPower p 1 x = algebraMap (Ainf p) (AcrisZero p) (x : Ainf p) := by
  apply Subtype.ext
  simp

theorem factorial_mul_dividedPower (n : ℕ) (x : RingHom.ker (theta p)) :
    (n.factorial : AcrisZero p) * dividedPower p n x =
      (algebraMap (Ainf p) (AcrisZero p) (x : Ainf p)) ^ n := by
  apply Subtype.ext
  change (n.factorial : FractionRing (Ainf p)) *
    ((algebraMap (Ainf p) (FractionRing (Ainf p)) (x : Ainf p)) ^ n /
      (n.factorial : FractionRing (Ainf p))) = _
  rw [mul_div_cancel₀ _ (by exact_mod_cast Nat.factorial_ne_zero n)]
  rfl

/-- `A_cris` is the `p`-adic completion of the concrete integral envelope. -/
abbrev Acris : Type :=
  AdicCompletion (Ideal.span {(p : AcrisZero p)}) (AcrisZero p)

instance acris_p_complete : IsAdicComplete (Ideal.span {(p : Acris p)}) (Acris p) := by
  have h := AdicCompletion.isAdicComplete_self
    (Ideal.span {(p : AcrisZero p)}) (Submodule.fg_span_singleton _)
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using h

/-- `B_cris⁺ = A_cris[1/p]`. The cyclotomic logarithm must subsequently
be inverted to obtain `B_cris`. -/
abbrev BcrisPlus : Type := Localization.Away (p : Acris p)

theorem p_isUnit_bcrisPlus : IsUnit (p : BcrisPlus p) := by
  simpa only [map_natCast] using
    (IsLocalization.Away.algebraMap_isUnit (R := Acris p) (S := BcrisPlus p) p)

/-- A useful integral estimate for convergence of divided-power logarithms. -/
theorem p_pow_dvd_factorial_mul (n : ℕ) : p ^ n ∣ (p * n).factorial := by
  induction n with
  | zero => simp
  | succ n hn =>
    have hd := Nat.mul_dvd_mul hn (Nat.dvd_factorial hp.out.pos (le_refl p))
    have ht := hd.trans (Nat.factorial_mul_factorial_dvd_factorial_add (p * n) p)
    simpa [pow_succ, Nat.mul_add] using ht

/-- The `k`th summand of `log(1+x)`, written integrally as
`(-1)^k k! γ_(k+1)(x)`. -/
def logTerm (x : RingHom.ker (theta p)) (k : ℕ) : AcrisZero p :=
  (-1) ^ k * (k.factorial : AcrisZero p) * dividedPower p (k + 1) x

theorem logTerm_mem_pow (x : RingHom.ker (theta p)) {n k : ℕ} (hk : p * n ≤ k) :
    logTerm p x k ∈ (Ideal.span {(p : AcrisZero p)}) ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hd : p ^ n ∣ k.factorial :=
    (p_pow_dvd_factorial_mul p n).trans (Nat.factorial_dvd_factorial hk)
  have hc : (p : AcrisZero p) ^ n ∣ (k.factorial : AcrisZero p) := by
    obtain ⟨a, ha⟩ := hd
    refine ⟨(a : AcrisZero p), ?_⟩
    rw [ha, Nat.cast_mul, Nat.cast_pow]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hc _) _

/-- The logarithm partial sum with enough terms to be accurate modulo `p^n`. -/
def logPartialSum (x : RingHom.ker (theta p)) (n : ℕ) : AcrisZero p :=
  ∑ k ∈ Finset.range (p * n), logTerm p x k

theorem logPartialSum_cauchy (x : RingHom.ker (theta p)) :
    AdicCompletion.IsAdicCauchy (Ideal.span {(p : AcrisZero p)})
      (AcrisZero p) (logPartialSum p x) := by
  rw [AdicCompletion.isAdicCauchy_iff]
  intro n
  apply SModEq.symm
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
  change logPartialSum p x (n + 1) - logPartialSum p x n ∈ _
  rw [logPartialSum, logPartialSum,
    ← Finset.sum_Ico_eq_sub _ (Nat.mul_le_mul_left p (Nat.le_succ n))]
  apply Ideal.sum_mem
  intro k hk
  exact logTerm_mem_pow p x (Finset.mem_Ico.mp hk).1

/-- The convergent divided-power logarithm as an actual element of `A_cris`. -/
def pdLog (x : RingHom.ker (theta p)) : Acris p :=
  AdicCompletion.mk (Ideal.span {(p : AcrisZero p)}) (AcrisZero p)
    ⟨logPartialSum p x, logPartialSum_cauchy p x⟩

theorem pdLog_eval (x : RingHom.ker (theta p)) (n : ℕ) :
    AdicCompletion.evalₐ (Ideal.span {(p : AcrisZero p)}) n (pdLog p x) =
      Ideal.Quotient.mk ((Ideal.span {(p : AcrisZero p)}) ^ n) (logPartialSum p x n) :=
  AdicCompletion.evalₐ_mk (Ideal.span {(p : AcrisZero p)}) n
    ⟨logPartialSum p x, logPartialSum_cauchy p x⟩

theorem exists_primitiveRoot_integer :
    ∃ ζ : 𝓞_ℂ_[p], IsPrimitiveRoot ζ p := by
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[p] p
  have hmem : z ∈ 𝓞_ℂ_[p] := complex_mem_integer_of_pow p 1 (by simpa using hz.pow_eq_one)
  refine ⟨⟨z, hmem⟩, ?_⟩
  constructor
  · exact Subtype.ext hz.pow_eq_one
  · intro n hn
    exact hz.dvd_of_pow_eq_one n (congrArg Subtype.val hn)

/-- A choice of primitive `p`th root in the actual ring of integers. -/
def primitiveRootInteger : 𝓞_ℂ_[p] := (exists_primitiveRoot_integer p).choose

theorem primitiveRootInteger_primitive : IsPrimitiveRoot (primitiveRootInteger p) p :=
  (exists_primitiveRoot_integer p).choose_spec

def integralPthRoot (x : 𝓞_ℂ_[p]) : 𝓞_ℂ_[p] := (complexInt_pow_surjective p x).choose

@[simp]
theorem integralPthRoot_pow (x : 𝓞_ℂ_[p]) : integralPthRoot p x ^ p = x :=
  (complexInt_pow_surjective p x).choose_spec

/-- A compatible sequence `1, ζ_p, ζ_(p²),...` of roots of unity. -/
def cyclotomicRootSequence : ℕ → 𝓞_ℂ_[p]
  | 0 => 1
  | n + 1 => (integralPthRoot p)^[n] (primitiveRootInteger p)

theorem cyclotomicRootSequence_compatible (n : ℕ) :
    cyclotomicRootSequence p (n + 1) ^ p = cyclotomicRootSequence p n := by
  cases n with
  | zero => exact (primitiveRootInteger_primitive p).pow_eq_one
  | succ n => simp [cyclotomicRootSequence, Function.iterate_succ_apply']

def cyclotomicRoots : Perfection 𝓞_ℂ_[p] p :=
  ⟨cyclotomicRootSequence p, cyclotomicRootSequence_compatible p⟩

/-- Reduction modulo `p` identifies compatible root sequences with the tilt. -/
def tiltMonoidEquiv : Perfection 𝓞_ℂ_[p] p ≃* PreTilt 𝓞_ℂ_[p] p :=
  Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])})

theorem untilt_tiltMonoidEquiv (x : Perfection 𝓞_ℂ_[p] p) :
    (tiltMonoidEquiv p x).untilt = Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 0 x := by
  exact Perfection.teichmuller₀_mapMonoidHom_idealQuotientMk
    (p := p) (I := Ideal.span {(p : 𝓞_ℂ_[p])}) (x := x)

/-- The standard cyclotomic element `ε` in the tilt. -/
def epsilon : PreTilt 𝓞_ℂ_[p] p :=
  tiltMonoidEquiv p (cyclotomicRoots p)

theorem epsilon_untilt : (epsilon p).untilt = 1 := by
  rw [epsilon, untilt_tiltMonoidEquiv]
  rfl

theorem epsilon_ne_one : epsilon p ≠ 1 := by
  intro h
  have heq :
      tiltMonoidEquiv p (cyclotomicRoots p) = tiltMonoidEquiv p 1 := by
    simpa only [epsilon, map_one] using h
  have hc := congrArg (Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 1)
    ((tiltMonoidEquiv p).injective heq)
  change primitiveRootInteger p = 1 at hc
  have hd := (primitiveRootInteger_primitive p).dvd_of_pow_eq_one 1 (by simp [hc])
  exact hp.out.ne_one (Nat.dvd_one.mp hd)

/-- The element `[ε] - 1` belongs to the kernel of Fontaine's theta map. -/
def cyclotomicKernelElement : RingHom.ker (theta p) :=
  ⟨WittVector.teichmuller p (epsilon p) - 1, by
    simp [RingHom.mem_ker, theta_teichmuller, epsilon_untilt]⟩

theorem cyclotomicKernelElement_ne_zero :
    (cyclotomicKernelElement p : Ainf p) ≠ 0 := by
  intro h
  have hw : WittVector.teichmuller p (epsilon p) = 1 := sub_eq_zero.mp h
  have he := congrArg (fun x : Ainf p => x.coeff 0) hw
  exact epsilon_ne_one p (by simpa only [WittVector.teichmuller_coeff_zero,
    WittVector.one_coeff_zero] using he)

/-- Fontaine's cyclotomic period, defined by the convergent divided-power logarithm. -/
def t : Acris p := pdLog p (cyclotomicKernelElement p)

/-- The actual crystalline period ring, constructed as `A_cris[1/p, 1/t]`.
No comparison isomorphism or fixed-scalar assertion is part of this definition. -/
abbrev Bcris : Type :=
  Localization.Away (algebraMap (Acris p) (BcrisPlus p) (t p))

theorem p_isUnit_bcris : IsUnit (p : Bcris p) := by
  simpa only [map_natCast] using
    (p_isUnit_bcrisPlus p).map (algebraMap (BcrisPlus p) (Bcris p))

theorem t_isUnit_bcris :
    IsUnit (algebraMap (BcrisPlus p) (Bcris p)
      (algebraMap (Acris p) (BcrisPlus p) (t p))) :=
  IsLocalization.Away.algebraMap_isUnit
    (S := Bcris p) (algebraMap (Acris p) (BcrisPlus p) (t p))

/-- The canonical `ℤ_p` constants in `A_inf`, obtained by mapping Witt vectors
from `𝔽_p` to the tilt. -/
def padicIntToAinf : ℤ_[p] →+* Ainf p :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (PreTilt 𝓞_ℂ_[p] p))).comp
    (WittVector.fromPadicInt p)

def padicIntToBcrisPlus : ℤ_[p] →+* BcrisPlus p :=
  (algebraMap (Acris p) (BcrisPlus p)).comp
    ((algebraMap (AcrisZero p) (Acris p)).comp
      ((algebraMap (Ainf p) (AcrisZero p)).comp (padicIntToAinf p)))

/-- Inverting `p` in the target makes every nonzero `p`-adic integer invertible. -/
theorem padicInt_map_nonzero_isUnit {S : Type*} [CommRing S]
    (f : ℤ_[p] →+* S) (hf : IsUnit (f p)) {x : ℤ_[p]} (hx : x ≠ 0) :
    IsUnit (f x) := by
  rw [PadicInt.unitCoeff_spec hx, map_mul, map_pow]
  exact ((PadicInt.unitCoeff hx).isUnit.map f).mul (hf.pow _)

/-- The `ℚ_p` constants in `B_cris⁺`, constructed using the universal property
of the fraction field of `ℤ_p`. -/
def padicFieldToBcrisPlus : ℚ_[p] →+* BcrisPlus p :=
  IsLocalization.lift (S := ℚ_[p]) (g := padicIntToBcrisPlus p)
    (fun y : nonZeroDivisors ℤ_[p] => padicInt_map_nonzero_isUnit p
      (padicIntToBcrisPlus p) (by simpa only [map_natCast] using p_isUnit_bcrisPlus p)
      (mem_nonZeroDivisors_iff_ne_zero.mp y.property))

@[simp]
theorem padicFieldToBcrisPlus_int (x : ℤ_[p]) :
    padicFieldToBcrisPlus p (algebraMap ℤ_[p] ℚ_[p] x) = padicIntToBcrisPlus p x :=
  IsLocalization.lift_eq _ x

instance bcrisPlus_padicAlgebra : Algebra ℚ_[p] (BcrisPlus p) :=
  (padicFieldToBcrisPlus p).toAlgebra

def padicFieldToBcris : ℚ_[p] →+* Bcris p :=
  (algebraMap (BcrisPlus p) (Bcris p)).comp (padicFieldToBcrisPlus p)

instance bcris_padicAlgebra : Algebra ℚ_[p] (Bcris p) :=
  (padicFieldToBcris p).toAlgebra

/-- Every endomorphism of `𝓞_ℂ_p` preserves `(p)` and acts on its reduction. -/
def modPMap (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) :
    ModP 𝓞_ℂ_[p] p →+* ModP 𝓞_ℂ_[p] p :=
  Ideal.quotientMap _ f (by
    rw [← Ideal.map_le_iff_le_comap]
    simp [Ideal.map_span])

@[simp]
theorem modPMap_mk (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (x : 𝓞_ℂ_[p]) :
    modPMap p f (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (f x) := rfl

/-- The induced map on the actual tilt. -/
def tiltMap (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) :
    PreTilt 𝓞_ℂ_[p] p →+* PreTilt 𝓞_ℂ_[p] p :=
  Perfection.map p (modPMap p f)

theorem tiltMap_rootSequence (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p])
    (x : Perfection 𝓞_ℂ_[p] p) :
    tiltMap p f (tiltMonoidEquiv p x) =
      tiltMonoidEquiv p (Perfection.mapMonoidHom p f x) := by
  apply Perfection.ext
  intro n
  rfl

theorem untilt_natural (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (x : PreTilt 𝓞_ℂ_[p] p) :
    (tiltMap p f x).untilt = f x.untilt := by
  obtain ⟨y, rfl⟩ := (tiltMonoidEquiv p).surjective x
  rw [tiltMap_rootSequence, untilt_tiltMonoidEquiv, untilt_tiltMonoidEquiv]
  rfl

/-- Functoriality of the integral period ring is induced by Witt functoriality. -/
def ainfMap (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) : Ainf p →+* Ainf p :=
  WittVector.map (tiltMap p f)

@[simp]
theorem ainfMap_teichmuller (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p])
    (x : PreTilt 𝓞_ℂ_[p] p) :
    ainfMap p f (WittVector.teichmuller p x) =
      WittVector.teichmuller p (tiltMap p f x) :=
  WittVector.map_teichmuller p (tiltMap p f) x

/-- Naturality of theta modulo each power of `p`, proved by the uniqueness
of maps out of Witt vectors into a ring where `p` is nilpotent. -/
theorem theta_natural_mod (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (n : ℕ) :
    (Ideal.Quotient.mk ((Ideal.span {(p : 𝓞_ℂ_[p])}) ^ n)).comp
        ((theta p).comp (ainfMap p f)) =
      (Ideal.Quotient.mk ((Ideal.span {(p : 𝓞_ℂ_[p])}) ^ n)).comp
        (f.comp (theta p)) := by
  apply WittVector.eq_of_apply_teichmuller_eq
  · refine ⟨n, ?_⟩
    have hmem : (p : 𝓞_ℂ_[p]) ^ n ∈ (Ideal.span {(p : 𝓞_ℂ_[p])}) ^ n :=
      Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) n
    simpa only [map_pow, map_natCast] using Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  · intro x
    simp only [RingHom.comp_apply, ainfMap_teichmuller, theta_teichmuller, untilt_natural]

/-- Theta is natural for endomorphisms of the coefficient ring. No action on
crystalline cohomology or comparison isomorphism is assumed here. -/
theorem theta_natural (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (x : Ainf p) :
    theta p (ainfMap p f x) = f (theta p x) := by
  rw [IsHausdorff.eq_iff_smodEq (I := Ideal.span {(p : 𝓞_ℂ_[p])})]
  simp only [smul_eq_mul, Ideal.mul_top]
  intro n
  have h := congrArg (fun h : Ainf p →+*
      (𝓞_ℂ_[p] ⧸ (Ideal.span {(p : 𝓞_ℂ_[p])}) ^ n) => h x)
    (theta_natural_mod p f n)
  simpa only [SModEq.idealQuotientMk, RingHom.comp_apply] using h

/-- The Galois-stable ideal used in the divided-power construction. -/
def thetaKernelMap (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p])
    (x : RingHom.ker (theta p)) : RingHom.ker (theta p) :=
  ⟨ainfMap p f x, by
    rw [RingHom.mem_ker, theta_natural, (RingHom.mem_ker.mp x.property), map_zero]⟩

@[simp]
theorem modPMap_id : modPMap p (RingHom.id 𝓞_ℂ_[p]) = RingHom.id _ := by
  ext x
  rfl

theorem modPMap_comp (f g : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) :
    modPMap p (g.comp f) = (modPMap p g).comp (modPMap p f) := by
  ext x
  rfl

@[simp]
theorem tiltMap_id : tiltMap p (RingHom.id 𝓞_ℂ_[p]) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  apply Perfection.ext
  intro n
  exact congrArg (fun f : ModP 𝓞_ℂ_[p] p →+* ModP 𝓞_ℂ_[p] p =>
    f (PreTilt.coeff n x)) (modPMap_id p)

theorem tiltMap_comp (f g : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) :
    tiltMap p (g.comp f) = (tiltMap p g).comp (tiltMap p f) := by
  apply RingHom.ext
  intro x
  apply Perfection.ext
  intro n
  exact congrArg (fun h : ModP 𝓞_ℂ_[p] p →+* ModP 𝓞_ℂ_[p] p =>
    h (PreTilt.coeff n x)) (modPMap_comp p f g)

@[simp]
theorem ainfMap_id : ainfMap p (RingHom.id 𝓞_ℂ_[p]) = RingHom.id _ := by
  ext x n
  exact congrArg (fun f : PreTilt 𝓞_ℂ_[p] p →+* PreTilt 𝓞_ℂ_[p] p =>
    f (x.coeff n)) (tiltMap_id p)

theorem ainfMap_comp (f g : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) :
    ainfMap p (g.comp f) = (ainfMap p g).comp (ainfMap p f) := by
  ext x n
  exact congrArg (fun h : PreTilt 𝓞_ℂ_[p] p →+* PreTilt 𝓞_ℂ_[p] p =>
    h (x.coeff n)) (tiltMap_comp p f g)

/-- An automorphism of `𝓞_ℂ_p` induces an automorphism of `A_inf`. -/
def ainfEquiv (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) : Ainf p ≃+* Ainf p :=
  { ainfMap p f.toRingHom with
    invFun := ainfMap p f.symm.toRingHom
    left_inv := fun x => by
      have h := congrArg (fun h : Ainf p →+* Ainf p => h x)
        (ainfMap_comp p f.toRingHom f.symm.toRingHom)
      have hf : f.symm.toRingHom.comp f.toRingHom = RingHom.id 𝓞_ℂ_[p] := by
        apply RingHom.ext
        intro z
        exact f.symm_apply_apply z
      rw [hf, ainfMap_id] at h
      exact h.symm
    right_inv := fun x => by
      have h := congrArg (fun h : Ainf p →+* Ainf p => h x)
        (ainfMap_comp p f.symm.toRingHom f.toRingHom)
      have hf : f.toRingHom.comp f.symm.toRingHom = RingHom.id 𝓞_ℂ_[p] := by
        apply RingHom.ext
        intro z
        exact f.apply_symm_apply z
      rw [hf, ainfMap_id] at h
      exact h.symm }

def ainfFractionEquiv (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) :
    FractionRing (Ainf p) ≃+* FractionRing (Ainf p) :=
  IsFractionRing.ringEquivOfRingEquiv (ainfEquiv p f)

@[simp]
theorem ainfFractionEquiv_algebraMap (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : Ainf p) :
    ainfFractionEquiv p f (algebraMap (Ainf p) (FractionRing (Ainf p)) x) =
      algebraMap (Ainf p) (FractionRing (Ainf p)) (ainfMap p f.toRingHom x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x

@[simp]
theorem ainfFractionEquiv_dividedPower (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p])
    (n : ℕ) (x : RingHom.ker (theta p)) :
    ainfFractionEquiv p f (dividedPower p n x : FractionRing (Ainf p)) =
      (dividedPower p n (thetaKernelMap p f.toRingHom x) : FractionRing (Ainf p)) := by
  simp only [dividedPower_coe, map_div₀, map_pow, map_natCast, ainfFractionEquiv_algebraMap]
  rfl

/-- Automorphisms preserve the concrete divided-power envelope because they
preserve theta's kernel and commute with the rational divided powers. -/
theorem ainfFractionEquiv_preserves_acrisZero (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p])
    {x : FractionRing (Ainf p)} (hx : x ∈ acrisZeroSubalgebra p) :
    ainfFractionEquiv p f x ∈ acrisZeroSubalgebra p := by
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
      obtain ⟨⟨n, z⟩, rfl⟩ := hy
      change ainfFractionEquiv p f (dividedPower p n z : FractionRing (Ainf p)) ∈ _
      rw [ainfFractionEquiv_dividedPower]
      exact (dividedPower p n (thetaKernelMap p f.toRingHom z)).property
  | algebraMap a =>
      rw [ainfFractionEquiv_algebraMap]
      exact (acrisZeroSubalgebra p).algebraMap_mem _
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact (acrisZeroSubalgebra p).add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
      rw [map_mul]
      exact (acrisZeroSubalgebra p).mul_mem ihx ihy

def acrisZeroMap (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) : AcrisZero p →+* AcrisZero p where
  toFun x := ⟨ainfFractionEquiv p f x, ainfFractionEquiv_preserves_acrisZero p f x.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' x y := Subtype.ext (map_add _ (x : FractionRing (Ainf p)) y)
  map_mul' x y := Subtype.ext (map_mul _ (x : FractionRing (Ainf p)) y)

@[simp]
theorem acrisZeroMap_dividedPower (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p])
    (n : ℕ) (x : RingHom.ker (theta p)) :
    acrisZeroMap p f (dividedPower p n x) =
      dividedPower p n (thetaKernelMap p f.toRingHom x) :=
  Subtype.ext (ainfFractionEquiv_dividedPower p f n x)

theorem ainfEquiv_symm (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) :
    ainfEquiv p f.symm = (ainfEquiv p f).symm := by
  apply RingEquiv.ext
  intro x
  rfl

theorem ainfFractionEquiv_symm (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) :
    ainfFractionEquiv p f.symm = (ainfFractionEquiv p f).symm := by
  simp only [ainfFractionEquiv, ainfEquiv_symm,
    IsFractionRing.ringEquivOfRingEquiv_symm]

def acrisZeroEquiv (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) : AcrisZero p ≃+* AcrisZero p :=
  { acrisZeroMap p f with
    invFun := acrisZeroMap p f.symm
    left_inv := fun x => by
      apply Subtype.ext
      change ainfFractionEquiv p f.symm (ainfFractionEquiv p f x) = x
      rw [ainfFractionEquiv_symm]
      exact (ainfFractionEquiv p f).symm_apply_apply x
    right_inv := fun x => by
      apply Subtype.ext
      change ainfFractionEquiv p f (ainfFractionEquiv p f.symm x) = x
      rw [ainfFractionEquiv_symm]
      exact (ainfFractionEquiv p f).apply_symm_apply x }

section CompletionMaps

omit hp
variable {S : Type*} [CommRing S]

def pPowerQuotientMap (f : S →+* S) (n : ℕ) :
    S ⧸ (Ideal.span {(p : S)}) ^ n →+* S ⧸ (Ideal.span {(p : S)}) ^ n :=
  Ideal.quotientMap _ f (by
    rw [← Ideal.map_le_iff_le_comap]
    simp [Ideal.map_pow, Ideal.map_span])

@[simp]
theorem pPowerQuotientMap_mk (f : S →+* S) (n : ℕ) (x : S) :
    pPowerQuotientMap p f n (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (f x) := rfl

@[simp]
theorem pPowerQuotientMap_id (n : ℕ) :
    pPowerQuotientMap p (RingHom.id S) n = RingHom.id _ := by
  ext x
  rfl

theorem pPowerQuotientMap_comp (f g : S →+* S) (n : ℕ) :
    pPowerQuotientMap p (g.comp f) n =
      (pPowerQuotientMap p g n).comp (pPowerQuotientMap p f n) := by
  ext x
  rfl

theorem pPowerQuotientMap_factorPow (f : S →+* S) {m n : ℕ} (h : m ≤ n)
    (x : S ⧸ (Ideal.span {(p : S)}) ^ n) :
    Ideal.Quotient.factorPow (Ideal.span {(p : S)}) h (pPowerQuotientMap p f n x) =
      pPowerQuotientMap p f m (Ideal.Quotient.factorPow (Ideal.span {(p : S)}) h x) := by
  induction x using Quotient.inductionOn' with
  | h x => rfl

theorem completionEval_factorPow {m n : ℕ} (h : m ≤ n)
    (x : AdicCompletion (Ideal.span {(p : S)}) S) :
    Ideal.Quotient.factorPow (Ideal.span {(p : S)}) h
        (AdicCompletion.evalₐ (Ideal.span {(p : S)}) n x) =
      AdicCompletion.evalₐ (Ideal.span {(p : S)}) m x := by
  induction x using AdicCompletion.induction_on (Ideal.span {(p : S)}) S with
  | h a =>
      rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
      exact AdicCompletion.Ideal.mk_eq_mk (Ideal.span {(p : S)}) h a

theorem pAdicMap_compatible (f : S →+* S) {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (Ideal.span {(p : S)}) h).comp
        ((pPowerQuotientMap p f n).comp
          (AdicCompletion.evalₐ (Ideal.span {(p : S)}) n).toRingHom) =
      (pPowerQuotientMap p f m).comp
        (AdicCompletion.evalₐ (Ideal.span {(p : S)}) m).toRingHom := by
  apply RingHom.ext
  intro x
  change Ideal.Quotient.factorPow _ h
      (pPowerQuotientMap p f n (AdicCompletion.evalₐ _ n x)) =
    pPowerQuotientMap p f m (AdicCompletion.evalₐ _ m x)
  rw [pPowerQuotientMap_factorPow, completionEval_factorPow]

/-- A ring endomorphism induces a map of its `p`-adic completion, constructed
on the compatible quotient rings. -/
def pAdicMap (f : S →+* S) :
    AdicCompletion (Ideal.span {(p : S)}) S →+*
      AdicCompletion (Ideal.span {(p : S)}) S :=
  AdicCompletion.liftRingHom (Ideal.span {(p : S)})
    (fun n => (pPowerQuotientMap p f n).comp
      (AdicCompletion.evalₐ (Ideal.span {(p : S)}) n).toRingHom)
    (pAdicMap_compatible p f)

@[simp]
theorem pAdicMap_eval (f : S →+* S)
    (x : AdicCompletion (Ideal.span {(p : S)}) S) (n : ℕ) :
    AdicCompletion.evalₐ (Ideal.span {(p : S)}) n (pAdicMap p f x) =
      pPowerQuotientMap p f n (AdicCompletion.evalₐ (Ideal.span {(p : S)}) n x) :=
  AdicCompletion.evalₐ_liftRingHom (Ideal.span {(p : S)})
    (fun n => (pPowerQuotientMap p f n).comp
      (AdicCompletion.evalₐ (Ideal.span {(p : S)}) n).toRingHom)
    (pAdicMap_compatible p f) n x

@[simp]
theorem pAdicMap_of (f : S →+* S) (x : S) :
    pAdicMap p f (AdicCompletion.of (Ideal.span {(p : S)}) S x) =
      AdicCompletion.of (Ideal.span {(p : S)}) S (f x) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  simp only [pAdicMap_eval, AdicCompletion.evalₐ_of, pPowerQuotientMap_mk]

@[simp]
theorem pAdicMap_id : pAdicMap p (RingHom.id S) = RingHom.id _ := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [pAdicMap_eval, pPowerQuotientMap_id]
  rfl

theorem pAdicMap_comp (f g : S →+* S) :
    pAdicMap p (g.comp f) = (pAdicMap p g).comp (pAdicMap p f) := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  change AdicCompletion.evalₐ _ n (pAdicMap p (g.comp f) x) =
    AdicCompletion.evalₐ _ n (pAdicMap p g (pAdicMap p f x))
  rw [pAdicMap_eval, pAdicMap_eval, pAdicMap_eval, pPowerQuotientMap_comp]
  rfl

/-- Ring automorphisms induce automorphisms of the actual `p`-adic completion. -/
def pAdicEquiv (f : S ≃+* S) :
    AdicCompletion (Ideal.span {(p : S)}) S ≃+*
      AdicCompletion (Ideal.span {(p : S)}) S :=
  { pAdicMap p f.toRingHom with
    invFun := pAdicMap p f.symm.toRingHom
    left_inv := fun x => by
      have h := congrArg (fun h : AdicCompletion (Ideal.span {(p : S)}) S →+*
          AdicCompletion (Ideal.span {(p : S)}) S => h x)
        (pAdicMap_comp p f.toRingHom f.symm.toRingHom)
      have hf : f.symm.toRingHom.comp f.toRingHom = RingHom.id S := by
        apply RingHom.ext
        intro z
        exact f.symm_apply_apply z
      rw [hf, pAdicMap_id] at h
      exact h.symm
    right_inv := fun x => by
      have h := congrArg (fun h : AdicCompletion (Ideal.span {(p : S)}) S →+*
          AdicCompletion (Ideal.span {(p : S)}) S => h x)
        (pAdicMap_comp p f.symm.toRingHom f.toRingHom)
      have hf : f.toRingHom.comp f.symm.toRingHom = RingHom.id S := by
        apply RingHom.ext
        intro z
        exact f.apply_symm_apply z
      rw [hf, pAdicMap_id] at h
      exact h.symm }

end CompletionMaps

/-- The induced map on the completed integral crystalline period ring. -/
def acrisMap (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) : Acris p →+* Acris p :=
  pAdicMap p (acrisZeroMap p f)

def acrisEquiv (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) : Acris p ≃+* Acris p :=
  pAdicEquiv p (acrisZeroEquiv p f)

/-- Inverting `p` extends the induced automorphism to `B_cris⁺`. -/
def bcrisPlusEquiv (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) : BcrisPlus p ≃+* BcrisPlus p :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (p : Acris p)) (T := Submonoid.powers (p : Acris p))
    (BcrisPlus p) (BcrisPlus p)
    (acrisEquiv p f) (by simp [Submonoid.map_powers])

theorem acrisZeroMap_logPartialSum (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p])
    (x : RingHom.ker (theta p)) (n : ℕ) :
    acrisZeroMap p f (logPartialSum p x n) =
      logPartialSum p (thetaKernelMap p f.toRingHom x) n := by
  simp only [logPartialSum, map_sum, logTerm, map_mul, map_pow, _root_.map_neg,
    map_one, map_natCast, acrisZeroMap_dividedPower]

/-- The actual convergent logarithm is natural for the induced ring maps. -/
theorem acrisMap_pdLog (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p])
    (x : RingHom.ker (theta p)) :
    acrisMap p f (pdLog p x) = pdLog p (thetaKernelMap p f.toRingHom x) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [acrisMap, pAdicMap_eval]
  simp only [pdLog_eval, pPowerQuotientMap_mk,
    acrisZeroMap_logPartialSum]

/-- The integral constants are fixed by the induced automorphisms of `A_inf`. -/
theorem ainfMap_padicInt (f : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]) (a : ℤ_[p]) :
    ainfMap p f (padicIntToAinf p a) = padicIntToAinf p a := by
  apply WittVector.ext
  intro n
  change tiltMap p f
      ((ZMod.castHom (dvd_refl p) (PreTilt 𝓞_ℂ_[p] p))
        ((WittVector.fromPadicInt p a).coeff n)) =
    (ZMod.castHom (dvd_refl p) (PreTilt 𝓞_ℂ_[p] p))
      ((WittVector.fromPadicInt p a).coeff n)
  exact congrArg (fun h : ZMod p →+* PreTilt 𝓞_ℂ_[p] p =>
    h ((WittVector.fromPadicInt p a).coeff n))
    (RingHom.ext_zmod
      ((tiltMap p f).comp (ZMod.castHom (dvd_refl p) (PreTilt 𝓞_ℂ_[p] p)))
      (ZMod.castHom (dvd_refl p) (PreTilt 𝓞_ℂ_[p] p)))

@[simp]
theorem acrisZeroMap_algebraMap (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : Ainf p) :
    acrisZeroMap p f (algebraMap (Ainf p) (AcrisZero p) x) =
      algebraMap (Ainf p) (AcrisZero p) (ainfMap p f.toRingHom x) :=
  Subtype.ext (ainfFractionEquiv_algebraMap p f x)

@[simp]
theorem acrisEquiv_algebraMap (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : AcrisZero p) :
    acrisEquiv p f (algebraMap (AcrisZero p) (Acris p) x) =
      algebraMap (AcrisZero p) (Acris p) (acrisZeroMap p f x) :=
  pAdicMap_of p (acrisZeroMap p f) x

@[simp]
theorem bcrisPlusEquiv_algebraMap (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : Acris p) :
    bcrisPlusEquiv p f (algebraMap (Acris p) (BcrisPlus p) x) =
      algebraMap (Acris p) (BcrisPlus p) (acrisEquiv p f x) := by
  unfold bcrisPlusEquiv
  rw [IsLocalization.ringEquivOfRingEquiv_eq]

theorem bcrisPlusEquiv_padicInt (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : ℤ_[p]) :
    bcrisPlusEquiv p f (padicIntToBcrisPlus p x) = padicIntToBcrisPlus p x := by
  simp only [padicIntToBcrisPlus, RingHom.comp_apply, bcrisPlusEquiv_algebraMap,
    acrisEquiv_algebraMap, acrisZeroMap_algebraMap, ainfMap_padicInt]

theorem bcrisPlusEquiv_padicField (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) (x : ℚ_[p]) :
    bcrisPlusEquiv p f (padicFieldToBcrisPlus p x) = padicFieldToBcrisPlus p x := by
  have h : (bcrisPlusEquiv p f).toRingHom.comp (padicFieldToBcrisPlus p) =
      padicFieldToBcrisPlus p := by
    apply IsLocalization.ringHom_ext (M := nonZeroDivisors ℤ_[p])
    apply RingHom.ext
    intro a
    change bcrisPlusEquiv p f (padicFieldToBcrisPlus p (algebraMap ℤ_[p] ℚ_[p] a)) =
      padicFieldToBcrisPlus p (algebraMap ℤ_[p] ℚ_[p] a)
    rw [padicFieldToBcrisPlus_int]
    exact bcrisPlusEquiv_padicInt p f a
  exact congrArg (fun h : ℚ_[p] →+* BcrisPlus p => h x) h

/-- The induced automorphism of `B_cris⁺` is linear over the actual `ℚ_p`
constants, with scalar compatibility proved from the Witt-vector construction. -/
def bcrisPlusAlgEquiv (f : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) :
    BcrisPlus p ≃ₐ[ℚ_[p]] BcrisPlus p :=
  { bcrisPlusEquiv p f with
    commutes' := bcrisPlusEquiv_padicField p f }

/-- The usual absolute Galois group, realized on the algebraic closure of `ℚ_p`. -/
abbrev PadicGalois := PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p

theorem algebraicGalois_isometry (σ : PadicGalois p) : Isometry σ := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  change spectralNorm ℚ_[p] (PadicAlgCl p) (σ x) =
    spectralNorm ℚ_[p] (PadicAlgCl p) x
  exact (spectralNorm_eq_of_equiv σ x).symm

/-- Extend an actual Galois automorphism to the completed algebraic closure. -/
def galoisComplexEquiv (σ : PadicGalois p) : ℂ_[p] ≃+* ℂ_[p] :=
  UniformSpace.Completion.mapRingEquiv σ.toRingEquiv
    (algebraicGalois_isometry p σ).continuous
    (algebraicGalois_isometry p σ.symm).continuous

theorem galoisComplex_isometry (σ : PadicGalois p) : Isometry (galoisComplexEquiv p σ) :=
  (algebraicGalois_isometry p σ).completion_map

theorem complex_mem_integer_iff_norm (x : ℂ_[p]) : x ∈ 𝓞_ℂ_[p] ↔ ‖x‖ ≤ 1 := by
  change Valued.v x ≤ 1 ↔ _
  rw [← NNReal.coe_le_coe, complex_valuation_norm]
  rfl

/-- Restrict a norm-preserving automorphism of `ℂ_p` to its ring of integers. -/
def restrictComplexEquiv (e : ℂ_[p] ≃+* ℂ_[p]) (he : ∀ x, ‖e x‖ = ‖x‖) :
    𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p] where
  toFun x := ⟨e x, by
    rw [complex_mem_integer_iff_norm, he]
    exact (complex_mem_integer_iff_norm p x).mp x.property⟩
  invFun x := ⟨e.symm x, by
    rw [complex_mem_integer_iff_norm, ← he, e.apply_symm_apply]
    exact (complex_mem_integer_iff_norm p x).mp x.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_add' x y := Subtype.ext (map_add e (x : ℂ_[p]) y)
  map_mul' x y := Subtype.ext (map_mul e (x : ℂ_[p]) y)

/-- The Galois automorphism of the actual coefficient ring. -/
def galoisIntegerEquiv (σ : PadicGalois p) : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p] :=
  restrictComplexEquiv p (galoisComplexEquiv p σ)
    ((AddMonoidHomClass.isometry_iff_norm (galoisComplexEquiv p σ)).mp
      (galoisComplex_isometry p σ))

/-- An actual Galois automorphism induces a `ℚ_p`-algebra automorphism of
the constructed `B_cris⁺`. Extension past `t` still needs cyclotomic equivariance. -/
def galoisBcrisPlusEquiv (σ : PadicGalois p) : BcrisPlus p ≃ₐ[ℚ_[p]] BcrisPlus p :=
  bcrisPlusAlgEquiv p (galoisIntegerEquiv p σ)

end NumberTheory.PadicHodge.PeriodInvariants.PeriodRing

namespace NumberTheory.PadicHodge.PeriodInvariants.PeriodRing.TiltDivisibility

/-!
# Divisibility in the actual tilt of O_Cp

Compatible ratios in the completed algebraic closure prove the divisibility
statement needed to describe the kernel of theta modulo p.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing
open scoped NNReal

variable (p : ℕ) [Fact p.Prime]

theorem complex_mem_integer_of_p_pow (a : 𝓞_ℂ_[p]) (n : ℕ) {z : ℂ_[p]}
    (hz : z ^ p ^ n = (a : ℂ_[p])) : z ∈ 𝓞_ℂ_[p] := by
  change Valued.v z ≤ 1
  apply (pow_le_one_iff_of_nonneg (show 0 ≤ (Valued.v z : ℝ≥0) from bot_le)
    (pow_ne_zero n (Fact.out : p.Prime).ne_zero)).mp
  rw [← map_pow, hz]
  exact a.property

theorem coefficient_pow_complex (x : Perfection 𝓞_ℂ_[p] p) (n : ℕ) :
    (x.val n : ℂ_[p]) ^ p ^ n = (x.val 0 : ℂ_[p]) :=
  congrArg (fun a : 𝓞_ℂ_[p] => (a : ℂ_[p]))
    (Perfection.coeffMonoidHom_pow_p_pow_self x n)

theorem coefficient_ne_zero (y : Perfection 𝓞_ℂ_[p] p) (hy : y.val 0 ≠ 0) (n : ℕ) :
    (y.val n : ℂ_[p]) ≠ 0 := by
  intro hn
  have h := coefficient_pow_complex p y n
  rw [hn, zero_pow (pow_ne_zero n (Fact.out : p.Prime).ne_zero)] at h
  exact hy (Subtype.ext h.symm)

theorem ratio_coefficient_integral (x y : Perfection 𝓞_ℂ_[p] p) (a : 𝓞_ℂ_[p])
    (hy : y.val 0 ≠ 0) (h : x.val 0 = y.val 0 * a) (n : ℕ) :
    (x.val n : ℂ_[p]) / (y.val n : ℂ_[p]) ∈ 𝓞_ℂ_[p] := by
  apply complex_mem_integer_of_p_pow p a n
  rw [div_pow, coefficient_pow_complex, coefficient_pow_complex]
  apply (div_eq_iff (coefficient_ne_zero p y hy 0)).mpr
  have hh := congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) h
  change (x.val 0 : ℂ_[p]) = (y.val 0 : ℂ_[p]) * (a : ℂ_[p]) at hh
  exact hh.trans (mul_comm _ _)

def perfectionQuotient (x y : Perfection 𝓞_ℂ_[p] p) (a : 𝓞_ℂ_[p])
    (hy : y.val 0 ≠ 0) (h : x.val 0 = y.val 0 * a) : Perfection 𝓞_ℂ_[p] p :=
  ⟨fun n => ⟨(x.val n : ℂ_[p]) / (y.val n : ℂ_[p]), ratio_coefficient_integral p x y a hy h n⟩,
    fun n => by
      apply Subtype.val_injective
      change ((x.val (n + 1) : ℂ_[p]) / (y.val (n + 1) : ℂ_[p])) ^ p =
        (x.val n : ℂ_[p]) / (y.val n : ℂ_[p])
      rw [div_pow]
      exact congrArg₂ (fun a b : ℂ_[p] => a / b)
        (congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) (x.property n))
        (congrArg (fun z : 𝓞_ℂ_[p] => (z : ℂ_[p])) (y.property n))⟩

theorem perfectionQuotient_spec (x y : Perfection 𝓞_ℂ_[p] p) (a : 𝓞_ℂ_[p])
    (hy : y.val 0 ≠ 0) (h : x.val 0 = y.val 0 * a) :
    y * perfectionQuotient p x y a hy h = x := by
  apply Perfection.extMonoid
  intro n
  apply Subtype.val_injective
  change (y.val n : ℂ_[p]) * ((x.val n : ℂ_[p]) / (y.val n : ℂ_[p])) = (x.val n : ℂ_[p])
  exact mul_div_cancel₀ (x.val n : ℂ_[p]) (coefficient_ne_zero p y hy n)

theorem tilt_dvd_of_untilt_dvd (x y : PreTilt 𝓞_ℂ_[p] p)
    (hy : y.untilt ≠ 0) (h : y.untilt ∣ x.untilt) : y ∣ x := by
  let xs := (tiltMonoidEquiv p).symm x
  let ys := (tiltMonoidEquiv p).symm y
  have hx0 : xs.val 0 = x.untilt := by
    have hh := untilt_tiltMonoidEquiv p xs
    change (tiltMonoidEquiv p xs).untilt = xs.val 0 at hh
    have ht : tiltMonoidEquiv p xs = x := (tiltMonoidEquiv p).apply_symm_apply x
    rw [ht] at hh
    exact hh.symm
  have hy0 : ys.val 0 = y.untilt := by
    have hh := untilt_tiltMonoidEquiv p ys
    change (tiltMonoidEquiv p ys).untilt = ys.val 0 at hh
    have ht : tiltMonoidEquiv p ys = y := (tiltMonoidEquiv p).apply_symm_apply y
    rw [ht] at hh
    exact hh.symm
  obtain ⟨a, ha⟩ := h
  have hys : ys.val 0 ≠ 0 := hy0 ▸ hy
  have hxy : xs.val 0 = ys.val 0 * a := by rw [hx0, hy0]; exact ha
  refine ⟨tiltMonoidEquiv p (perfectionQuotient p xs ys a hys hxy), ?_⟩
  have he := congrArg (tiltMonoidEquiv p) (perfectionQuotient_spec p xs ys a hys hxy)
  simpa only [map_mul, xs, ys, MulEquiv.apply_symm_apply] using he.symm

def pRoots : Perfection 𝓞_ℂ_[p] p :=
  ⟨fun n => (integralPthRoot p)^[n] (p : 𝓞_ℂ_[p]), fun n => by
    dsimp only
    rw [Function.iterate_succ_apply', integralPthRoot_pow]⟩

def pTilt : PreTilt 𝓞_ℂ_[p] p := tiltMonoidEquiv p (pRoots p)

theorem pTilt_untilt : (pTilt p).untilt = (p : 𝓞_ℂ_[p]) :=
  untilt_tiltMonoidEquiv p (pRoots p)

theorem pTilt_dvd_of_coeff_zero (x : PreTilt 𝓞_ℂ_[p] p) (hx : PreTilt.coeff 0 x = 0) :
    pTilt p ∣ x := by
  apply tilt_dvd_of_untilt_dvd p x (pTilt p)
  · rw [pTilt_untilt]
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  · rw [pTilt_untilt]
    apply Ideal.mem_span_singleton.mp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [PreTilt.mk_untilt_eq_coeff_zero, hx]

end NumberTheory.PadicHodge.PeriodInvariants.PeriodRing.TiltDivisibility

end

end OAI
