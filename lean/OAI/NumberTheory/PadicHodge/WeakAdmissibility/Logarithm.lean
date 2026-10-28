import Mathlib

/-! # Logarithm -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings

/-!
Actual period-ring foundations for WeakAdmissibility, specialized to the ring of integers
of the completed algebraic closure of ℚ_p. No admissibility or Frobenius
fixed-vector vanishing is assumed in this file.
-/

open scoped NNReal
open Filter _root_.Topology

variable (p : ℕ) [Fact p.Prime]

theorem valuation_eq_nnnorm (x : ℂ_[p]) :
    (Valued.v x : ℝ≥0) = ‖x‖₊ := by
  apply NNReal.coe_injective
  change ((Valued.v x : ℝ≥0) : ℝ) = ‖x‖
  rw [PadicComplex.norm_eq_norm, Valuation.norm_def,
    PadicComplex.RankOne.hom_eq_embedding,
    Valuation.embedding_restrict]

theorem integer_norm_le_one (x : 𝓞_ℂ_[p]) : ‖(x : ℂ_[p])‖ ≤ 1 := by
  have h := x.property
  change (Valued.v (x : ℂ_[p]) : ℝ≥0) ≤ 1 at h
  rw [valuation_eq_nnnorm] at h
  exact_mod_cast h

theorem not_isUnit_p : ¬ IsUnit (p : 𝓞_ℂ_[p]) := by
  intro h
  have hv := (PadicComplexInt.integers p).one_of_isUnit h
  rw [map_natCast, PadicComplex.valuation_p, one_div, inv_eq_one, Nat.cast_eq_one] at hv
  exact (Fact.out : p.Prime).ne_one hv

instance p_not_isUnit : Fact (¬ IsUnit (p : 𝓞_ℂ_[p])) := ⟨not_isUnit_p p⟩

theorem integers_isClosed : IsClosed (PadicComplexInt p : Set ℂ_[p]) :=
  Valued.isClosed_valuationSubring ℂ_[p]

instance integers_complete : CompleteSpace 𝓞_ℂ_[p] :=
  (integers_isClosed p).completeSpace_coe

theorem norm_p : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  have h := congrArg (fun x : ℝ≥0 => (x : ℝ)) (PadicComplex.valuation_p p)
  simpa only [valuation_eq_nnnorm, NNReal.coe_inv, NNReal.coe_natCast,
    one_div, coe_nnnorm] using h

theorem norm_p_pos : 0 < ‖(p : ℂ_[p])‖ := by
  rw [norm_p]
  exact inv_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  rw [norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

theorem mem_p_power_iff (n : ℕ) (x : 𝓞_ℂ_[p]) :
    x ∈ (Ideal.span {(p : 𝓞_ℂ_[p])}) ^ n ↔
      ‖(x : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ n := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    (PadicComplexInt.integers p).dvd_iff_le, map_pow, map_natCast,
    Valuation.map_pow, valuation_eq_nnnorm, valuation_eq_nnnorm]
  exact_mod_cast (Iff.rfl : ‖(x : ℂ_[p])‖₊ ≤ ‖(p : ℂ_[p])‖₊ ^ n ↔ _)

theorem integers_isAdic : IsAdic (Ideal.span {(p : 𝓞_ℂ_[p])}) := by
  apply isAdic_iff.mpr
  constructor
  · intro n
    have heq : (↑((Ideal.span {(p : 𝓞_ℂ_[p])}) ^ n : Ideal 𝓞_ℂ_[p]) : Set 𝓞_ℂ_[p]) =
        (fun x : 𝓞_ℂ_[p] => (x : ℂ_[p])) ⁻¹'
          Metric.closedBall (0 : ℂ_[p]) (‖(p : ℂ_[p])‖ ^ n) := by
      ext x
      simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
        SetLike.mem_coe, mem_p_power_iff]
    rw [heq]
    exact (IsUltrametricDist.isOpen_closedBall (0 : ℂ_[p])
      (ne_of_gt (pow_pos (norm_p_pos p) n))).preimage continuous_subtype_val
  · intro s hs
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
    have ht : Tendsto (fun n : ℕ => ‖(p : ℂ_[p])‖ ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (norm_p_lt_one p)
    obtain ⟨n, hn⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 ε hε)
    refine ⟨n, fun x hx => hball ?_⟩
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt ((mem_p_power_iff p n x).mp hx) (hn n le_rfl)

instance integers_adicComplete :
    IsAdicComplete (Ideal.span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] :=
  (integers_isAdic p).isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

theorem integers_pow_surjective :
    Function.Surjective (fun x : 𝓞_ℂ_[p] => x ^ p) := by
  intro x
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x : ℂ_[p]) (Fact.out : p.Prime).pos
  have hynorm : ‖y‖ ≤ 1 := by
    apply (pow_le_one_iff_of_nonneg (norm_nonneg y) (Fact.out : p.Prime).ne_zero).mp
    rw [← norm_pow, hy]
    exact integer_norm_le_one p x
  have hyint : y ∈ PadicComplexInt p := by
    change (Valued.v y : ℝ≥0) ≤ 1
    rw [valuation_eq_nnnorm]
    exact_mod_cast hynorm
  refine ⟨⟨y, hyint⟩, ?_⟩
  apply Subtype.ext
  exact hy

theorem modP_frobenius_surjective :
    Function.Surjective (frobenius (ModP 𝓞_ℂ_[p] p) p) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨b, hb⟩ := integers_pow_surjective p a
  change b ^ p = a at hb
  refine ⟨Ideal.Quotient.mk _ b, ?_⟩
  rw [frobenius_def, ← map_pow, hb]

/-- The actual integral Fontaine ring for ℂ_p. -/
abbrev AInf := WittVector p (PreTilt 𝓞_ℂ_[p] p)

instance preTilt_isDomain : IsDomain (PreTilt 𝓞_ℂ_[p] p) :=
  PreTilt.isDomain ℂ_[p] (PadicComplex.valued p).v 𝓞_ℂ_[p]
    (PadicComplexInt.integers p) p

instance aInf_isDomain : IsDomain (AInf p) := inferInstance

/-- The actual rational Fontaine ring before completion along ker θ. -/
abbrev BInf := Localization.Away (p : AInf p)

/-- Fontaine's canonical theta map, with completeness discharged above. -/
def theta : AInf p →+* 𝓞_ℂ_[p] := WittVector.fontaineTheta 𝓞_ℂ_[p] p

theorem theta_surjective : Function.Surjective (theta p) :=
  surjective_fontaineTheta (modP_frobenius_surjective p)

/-- Reduction of theta modulo p. Its kernel is the ideal used for the
canonical p-adic divided-power envelope. -/
def thetaModP : AInf p →+* ModP 𝓞_ℂ_[p] p :=
  (Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p])})).comp (theta p)

theorem thetaModP_eq (x : AInf p) :
    thetaModP p x = PreTilt.coeff 0 (x.coeff 0) :=
  WittVector.mk_fontaineTheta x

/-- Frobenius on the actual integral Fontaine ring. -/
def aInfFrobenius : AInf p ≃+* AInf p :=
  WittVector.frobeniusEquiv p (PreTilt 𝓞_ℂ_[p] p)

theorem thetaModP_frobenius (x : AInf p) :
    thetaModP p (aInfFrobenius p x) = thetaModP p x ^ p := by
  rw [thetaModP_eq, thetaModP_eq]
  change PreTilt.coeff 0 ((WittVector.frobenius x).coeff 0) = _
  rw [WittVector.coeff_frobenius_charP, map_pow]

/-- Rational ambient field used to construct the divided-power hull. -/
abbrev AInfFractionField := FractionRing (AInf p)

/-- The generators x^n/n!, for x in ker(θ mod p). -/
def dividedPowerGenerators : Set (AInfFractionField p) :=
  {z | ∃ (x : AInf p) (n : ℕ), thetaModP p x = 0 ∧
    z = algebraMap (AInf p) (AInfFractionField p) x ^ n / (n.factorial : AInfFractionField p)}

/-- The uncompleted crystalline envelope inside the fraction field of A_inf.
We use the canonical thickening A_inf → O_Cp/p, so divided powers of p
are included together with those of ker θ. -/
def aCrisUncompleted : Subalgebra (AInf p) (AInfFractionField p) :=
  Algebra.adjoin (AInf p) (dividedPowerGenerators p)

abbrev ACrisUncompleted := ↥(aCrisUncompleted p)

theorem dividedPower_mem (x : AInf p) (n : ℕ) (hx : thetaModP p x = 0) :
    algebraMap (AInf p) (AInfFractionField p) x ^ n / (n.factorial : AInfFractionField p)
      ∈ aCrisUncompleted p :=
  Algebra.subset_adjoin ⟨x, n, hx, rfl⟩

theorem thetaKernel_dividedPower_mem (x : AInf p) (n : ℕ) (hx : theta p x = 0) :
    algebraMap (AInf p) (AInfFractionField p) x ^ n / (n.factorial : AInfFractionField p)
      ∈ aCrisUncompleted p := by
  apply dividedPower_mem
  simp [thetaModP, hx]

/-- The p-adically completed crystalline envelope. -/
abbrev ACris := AdicCompletion
  (Ideal.span {(p : ACrisUncompleted p)}) (ACrisUncompleted p)

/-- The positive crystalline period ring A_cris[1/p]. -/
abbrev BCrisPlus := Localization.Away (p : ACris p)

/-- Frobenius on the ambient fraction field. Restriction to A_cris
requires proving preservation of the divided-power envelope. -/
def fractionFrobenius : AInfFractionField p ≃+* AInfFractionField p :=
  IsFractionRing.ringEquivOfRingEquiv (aInfFrobenius p)

theorem fractionFrobenius_algebraMap (x : AInf p) :
    fractionFrobenius p (algebraMap (AInf p) (AInfFractionField p) x) =
      algebraMap (AInf p) (AInfFractionField p) (aInfFrobenius p x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x

theorem frobenius_preserves_envelope {x : AInfFractionField p}
    (hx : x ∈ aCrisUncompleted p) :
    fractionFrobenius p x ∈ aCrisUncompleted p := by
  induction hx using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨x, n, hx, rfl⟩ := hz
    rw [map_div₀, map_pow, map_natCast, fractionFrobenius_algebraMap]
    apply dividedPower_mem
    rw [thetaModP_frobenius, hx, zero_pow (Fact.out : p.Prime).ne_zero]
  | algebraMap r =>
    rw [fractionFrobenius_algebraMap]
    exact (aCrisUncompleted p).algebraMap_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (aCrisUncompleted p).add_mem hx hy
  | mul x y _ _ hx hy =>
    rw [map_mul]
    exact (aCrisUncompleted p).mul_mem hx hy

/-- Actual Frobenius restricted to the crystalline envelope. -/
def aCrisUncompletedFrobenius : ACrisUncompleted p →+* ACrisUncompleted p where
  toFun x := ⟨fractionFrobenius p x, frobenius_preserves_envelope p x.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' x y := Subtype.ext (map_add (fractionFrobenius p)
    (x : AInfFractionField p) (y : AInfFractionField p))
  map_mul' x y := Subtype.ext (map_mul (fractionFrobenius p)
    (x : AInfFractionField p) (y : AInfFractionField p))

section CompletionMap

variable {R : Type*} [CommRing R] (I : Ideal R)
  (f : R →+* R) (hI : I.map f ≤ I)

include hI in
theorem map_preserves_ideal_pow (n : ℕ) : I ^ n ≤ (I ^ n).comap f := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact pow_le_pow_left' hI n

def completionMapComponent (n : ℕ) : AdicCompletion I R →+* R ⧸ I ^ n :=
  (Ideal.quotientMap (I ^ n) f (map_preserves_ideal_pow I f hI n)).comp
    (AdicCompletion.evalₐ I n).toRingHom

theorem completionMapComponent_compatible {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow I h).comp (completionMapComponent I f hI n) =
      completionMapComponent I f hI m := by
  ext x
  apply AdicCompletion.induction_on I R x
  intro c
  simp only [completionMapComponent, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, AdicCompletion.evalₐ_mk, Ideal.quotientMap_mk,
    Ideal.Quotient.factor_mk]
  apply Ideal.Quotient.eq.mpr
  have hc : c.val n - c.val m ∈ I ^ m := by
    simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using (c.property h).symm
  have hf := map_preserves_ideal_pow I f hI m hc
  simpa only [Ideal.mem_comap, map_sub] using hf

/-- A ring endomorphism preserving an ideal extends to its adic completion. -/
def completionMap : AdicCompletion I R →+* AdicCompletion I R :=
  AdicCompletion.liftRingHom I (completionMapComponent I f hI)
    (fun h => completionMapComponent_compatible I f hI h)

theorem completionMap_of (x : R) :
    completionMap I f hI (AdicCompletion.of I R x) = AdicCompletion.of I R (f x) := by
  apply AdicCompletion.ext_evalₐ
  intro n
  simp [completionMap, completionMapComponent]

end CompletionMap

theorem aCrisUncompletedFrobenius_preserves_p :
    (Ideal.span {(p : ACrisUncompleted p)}).map (aCrisUncompletedFrobenius p) ≤
      Ideal.span {(p : ACrisUncompleted p)} := by
  rw [Ideal.map_span]
  simp

/-- Actual Frobenius on A_cris, extended through p-adic completion. -/
def aCrisFrobenius : ACris p →+* ACris p :=
  completionMap (Ideal.span {(p : ACrisUncompleted p)})
    (aCrisUncompletedFrobenius p) (aCrisUncompletedFrobenius_preserves_p p)

/-- Actual Frobenius on B_cris^+ obtained by inverting p. -/
def bCrisPlusFrobenius : BCrisPlus p →+* BCrisPlus p :=
  Localization.awayLift
    ((algebraMap (ACris p) (BCrisPlus p)).comp (aCrisFrobenius p)) (p : ACris p)
    (by simpa using IsLocalization.Away.algebraMap_isUnit (p : ACris p))

theorem bCrisPlusFrobenius_algebraMap (x : ACris p) :
    bCrisPlusFrobenius p (algebraMap (ACris p) (BCrisPlus p) x) =
      algebraMap (ACris p) (BCrisPlus p) (aCrisFrobenius p x) :=
  IsLocalization.Away.lift_eq (p : ACris p)
    (by simpa using IsLocalization.Away.algebraMap_isUnit (p : ACris p)) x

/-- The canonical coefficient map ℤ_p → A_inf. -/
def padicIntToAInf : ℤ_[p] →+* AInf p :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (PreTilt 𝓞_ℂ_[p] p))).comp
    (WittVector.equiv p).symm.toRingHom

theorem padicIntToAInf_injective : Function.Injective (padicIntToAInf p) :=
  (WittVector.map_injective _
    (ZMod.castHom (dvd_refl p) (PreTilt 𝓞_ℂ_[p] p)).injective).comp
    (WittVector.equiv p).symm.injective

/-- The canonical coefficient embedding into the ambient fraction field. -/
def padicToFractionField : ℚ_[p] →+* AInfFractionField p :=
  IsFractionRing.lift (A := ℤ_[p]) (K := ℚ_[p])
    (g := (algebraMap (AInf p) (AInfFractionField p)).comp (padicIntToAInf p))
    ((IsFractionRing.injective (AInf p) (AInfFractionField p)).comp
      (padicIntToAInf_injective p))

theorem padicToFractionField_of_integer (x : ℤ_[p]) :
    padicToFractionField p (algebraMap ℤ_[p] ℚ_[p] x) =
      algebraMap (AInf p) (AInfFractionField p) (padicIntToAInf p x) :=
  IsFractionRing.lift_algebraMap _ x

instance aInf_charZero : CharZero (AInf p) :=
  (RingHom.charZero_iff (padicIntToAInf_injective p)).mp inferInstance

instance fractionField_charZero : CharZero (AInfFractionField p) :=
  (RingHom.charZero_iff (padicToFractionField p).injective).mp inferInstance

def dividedPower (x : AInf p) (n : ℕ) (hx : thetaModP p x = 0) : ACrisUncompleted p :=
  ⟨_, dividedPower_mem p x n hx⟩

/-- The term (-1)^n x^(n+1)/(n+1), written integrally using divided powers. -/
def crystallineLogTerm (x : AInf p) (hx : thetaModP p x = 0) (n : ℕ) :
    ACrisUncompleted p :=
  (-1) ^ n * (n.factorial : ACrisUncompleted p) * dividedPower p x (n + 1) hx

theorem crystallineLogTerm_coe (x : AInf p) (hx : thetaModP p x = 0) (n : ℕ) :
    (crystallineLogTerm p x hx n : AInfFractionField p) =
      (-1 : AInfFractionField p) ^ n *
        algebraMap (AInf p) (AInfFractionField p) x ^ (n + 1) / (n + 1 : AInfFractionField p) := by
  change ((-1 : AInfFractionField p) ^ n * (n.factorial : AInfFractionField p)) *
    (algebraMap (AInf p) (AInfFractionField p) x ^ (n + 1) /
      ((n + 1).factorial : AInfFractionField p)) = _
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hfact : (n.factorial : AInfFractionField p) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  field_simp [hfact]

theorem pow_dvd_factorial_multiple (k : ℕ) : p ^ k ∣ (p * k).factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Nat.mul_succ]
    exact (Nat.mul_dvd_mul ih ((Fact.out : p.Prime).dvd_factorial.mpr le_rfl)).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add (p * k) p)

theorem crystallineLogTerm_mem (x : AInf p) (hx : thetaModP p x = 0)
    (k n : ℕ) (hn : p * k ≤ n) :
    crystallineLogTerm p x hx n ∈ (Ideal.span {(p : ACrisUncompleted p)}) ^ k := by
  have hd : p ^ k ∣ n.factorial :=
    (pow_dvd_factorial_multiple p k).trans (Nat.factorial_dvd_factorial hn)
  have hfact : (n.factorial : ACrisUncompleted p) ∈
      (Ideal.span {(p : ACrisUncompleted p)}) ^ k := by
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    obtain ⟨c, hc⟩ := hd
    refine ⟨(c : ACrisUncompleted p), ?_⟩
    simpa only [Nat.cast_mul, Nat.cast_pow] using
      congrArg (fun n : ℕ => (n : ACrisUncompleted p)) hc
  exact ((Ideal.span {(p : ACrisUncompleted p)}) ^ k).mul_mem_right _
    (((Ideal.span {(p : ACrisUncompleted p)}) ^ k).mul_mem_left _ hfact)

/-- The crystalline logarithm is defined by a proved p-adic Cauchy sequence. -/
def crystallineLogCauchy (x : AInf p) (hx : thetaModP p x = 0) :
    AdicCompletion.AdicCauchySequence
      (Ideal.span {(p : ACrisUncompleted p)}) (ACrisUncompleted p) := by
  refine ⟨fun k => ∑ n ∈ Finset.range (p * k), crystallineLogTerm p x hx n, ?_⟩
  intro m n hmn
  change (Submodule.mkQ _)
      (∑ i ∈ Finset.range (p * m), crystallineLogTerm p x hx i) =
    (Submodule.mkQ _)
      (∑ i ∈ Finset.range (p * n), crystallineLogTerm p x hx i)
  rw [map_sum, map_sum]
  apply Finset.sum_subset (Finset.range_mono (Nat.mul_le_mul_left p hmn))
  intro i _ hi
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  have hbound : p * m ≤ i := Nat.le_of_not_gt (by simpa using hi)
  simpa only [smul_eq_mul, Ideal.mul_top] using crystallineLogTerm_mem p x hx m i hbound

/-- log(1+x) in A_cris for x in the kernel of theta modulo p. -/
def crystallineLog (x : AInf p) (hx : thetaModP p x = 0) : ACris p :=
  AdicCompletion.mk (Ideal.span {(p : ACrisUncompleted p)}) (ACrisUncompleted p)
    (crystallineLogCauchy p x hx)

theorem crystallineLog_mod (x : AInf p) (hx : thetaModP p x = 0) (k : ℕ) :
    AdicCompletion.evalₐ (Ideal.span {(p : ACrisUncompleted p)}) k
      (crystallineLog p x hx) =
        Ideal.Quotient.mk _
          (∑ n ∈ Finset.range (p * k), crystallineLogTerm p x hx n) :=
  AdicCompletion.evalₐ_mk (Ideal.span {(p : ACrisUncompleted p)}) k
    (crystallineLogCauchy p x hx)

theorem frobenius_kernel (x : AInf p) (hx : thetaModP p x = 0) :
    thetaModP p (aInfFrobenius p x) = 0 := by
  rw [thetaModP_frobenius, hx, zero_pow (Fact.out : p.Prime).ne_zero]

theorem frobenius_dividedPower (x : AInf p) (n : ℕ) (hx : thetaModP p x = 0) :
    aCrisUncompletedFrobenius p (dividedPower p x n hx) =
      dividedPower p (aInfFrobenius p x) n (frobenius_kernel p x hx) := by
  apply Subtype.ext
  change fractionFrobenius p
      (algebraMap (AInf p) (AInfFractionField p) x ^ n / (n.factorial : AInfFractionField p)) = _
  rw [map_div₀, map_pow, map_natCast, fractionFrobenius_algebraMap]
  rfl

theorem frobenius_crystallineLogTerm (x : AInf p) (hx : thetaModP p x = 0) (n : ℕ) :
    aCrisUncompletedFrobenius p (crystallineLogTerm p x hx n) =
      crystallineLogTerm p (aInfFrobenius p x) (frobenius_kernel p x hx) n := by
  simp only [crystallineLogTerm, map_mul, map_pow, map_neg, map_one, map_natCast,
    frobenius_dividedPower]

/-- Frobenius commutes with the constructed crystalline logarithm. -/
theorem frobenius_crystallineLog (x : AInf p) (hx : thetaModP p x = 0) :
    aCrisFrobenius p (crystallineLog p x hx) =
      crystallineLog p (aInfFrobenius p x) (frobenius_kernel p x hx) := by
  apply AdicCompletion.ext_evalₐ
  intro k
  rw [aCrisFrobenius, completionMap, AdicCompletion.evalₐ_liftRingHom]
  simp only [completionMapComponent, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom,
    crystallineLog_mod, Ideal.quotientMap_mk, map_sum, frobenius_crystallineLogTerm]

def integerRoot (x : 𝓞_ℂ_[p]) : 𝓞_ℂ_[p] := (integers_pow_surjective p x).choose

theorem integerRoot_pow (x : 𝓞_ℂ_[p]) : integerRoot p x ^ p = x :=
  (integers_pow_surjective p x).choose_spec

def firstCyclotomicRoot : ℂ_[p] :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[p] p).choose

theorem firstCyclotomicRoot_primitive : IsPrimitiveRoot (firstCyclotomicRoot p) p :=
  (HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[p] p).choose_spec

theorem firstCyclotomicRoot_integral : firstCyclotomicRoot p ∈ PadicComplexInt p := by
  have hn : ‖firstCyclotomicRoot p‖ ≤ 1 := by
    apply (pow_le_one_iff_of_nonneg (norm_nonneg _) (Fact.out : p.Prime).ne_zero).mp
    rw [← norm_pow, (firstCyclotomicRoot_primitive p).pow_eq_one, norm_one]
  change (Valued.v (firstCyclotomicRoot p) : ℝ≥0) ≤ 1
  rw [valuation_eq_nnnorm]
  exact_mod_cast hn

def firstCyclotomicInteger : 𝓞_ℂ_[p] :=
  ⟨firstCyclotomicRoot p, firstCyclotomicRoot_integral p⟩

theorem firstCyclotomicInteger_pow : firstCyclotomicInteger p ^ p = 1 :=
  Subtype.ext (firstCyclotomicRoot_primitive p).pow_eq_one

theorem firstCyclotomicInteger_ne_one : firstCyclotomicInteger p ≠ 1 := by
  intro h
  apply (firstCyclotomicRoot_primitive p).ne_one (Fact.out : p.Prime).one_lt
  exact congrArg (fun x : 𝓞_ℂ_[p] => (x : ℂ_[p])) h

/-- An actual compatible system of p-power roots of unity, starting with 1
and with a primitive p-th root in degree one. -/
def cyclotomicTower : Perfection 𝓞_ℂ_[p] p := by
  refine ⟨fun n => match n with
    | 0 => 1
    | n + 1 => (integerRoot p)^[n] (firstCyclotomicInteger p), ?_⟩
  intro n
  cases n with
  | zero => exact firstCyclotomicInteger_pow p
  | succ n =>
    dsimp only
    rw [Function.iterate_succ_apply', integerRoot_pow]

/-- The cyclotomic element ε in the actual tilt. -/
def epsilon : PreTilt 𝓞_ℂ_[p] p :=
  Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])}) (cyclotomicTower p)

theorem epsilon_untilt : PreTilt.untilt (epsilon p) = 1 := by
  have h := Perfection.coeff_zero_symm_quotientMulEquiv
    (p := p) (I := Ideal.span {(p : 𝓞_ℂ_[p])}) (epsilon p)
  rw [epsilon, MulEquiv.symm_apply_apply] at h
  exact h.symm

theorem epsilon_ne_one : epsilon p ≠ 1 := by
  intro h
  have ht : cyclotomicTower p = 1 := by
    apply (Perfection.quotientMulEquiv p (Ideal.span {(p : 𝓞_ℂ_[p])})).injective
    exact h
  have h₁ := congrArg (Perfection.coeffMonoidHom 𝓞_ℂ_[p] p 1) ht
  exact firstCyclotomicInteger_ne_one p h₁

def cyclotomicDifference : AInf p := WittVector.teichmuller p (epsilon p) - 1

theorem cyclotomicDifference_theta : theta p (cyclotomicDifference p) = 0 := by
  simp [theta, cyclotomicDifference, WittVector.fontaineTheta_teichmuller, epsilon_untilt]

theorem cyclotomicDifference_thetaModP : thetaModP p (cyclotomicDifference p) = 0 := by
  simp [thetaModP, cyclotomicDifference_theta]

theorem cyclotomicDifference_ne_zero : cyclotomicDifference p ≠ 0 := by
  intro h
  have he : WittVector.teichmuller p (epsilon p) = 1 := sub_eq_zero.mp h
  have hc := congrArg (fun x : AInf p => x.coeff 0) he
  apply epsilon_ne_one p
  simpa using hc

theorem frobenius_cyclotomicDifference :
    aInfFrobenius p (cyclotomicDifference p) =
      (1 + cyclotomicDifference p) ^ p - 1 := by
  rw [cyclotomicDifference, map_sub, map_one]
  change WittVector.frobenius (WittVector.teichmuller p (epsilon p)) - 1 = _
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def,
    map_pow]
  congr 2
  simp

/-- The actual cyclotomic period t = log([ε]), defined through proved convergence. -/
def cyclotomicPeriod : ACris p :=
  crystallineLog p (cyclotomicDifference p) (cyclotomicDifference_thetaModP p)

/-- Fontaine's crystalline period ring, inverting the cyclotomic period.
DeRhamLog and FullComparison prove nonvanishing and construct the
completed de Rham comparison for this ring. -/
abbrev BCris := Localization.Away
  (algebraMap (ACris p) (BCrisPlus p) (cyclotomicPeriod p))

/-- Fontaine's actual de Rham period rings, using mathlib's definitions. -/
abbrev BdRPlus := BDeRhamPlus 𝓞_ℂ_[p] p

abbrev BdR := BDeRham 𝓞_ℂ_[p] p

end NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings

namespace NumberTheory.PadicHodge.WeakAdmissibility.Logarithm

/-!
Logarithm identities used in the cyclotomic-period calculation for WeakAdmissibility.
The power-series identities below do not assume any identity in B_cris.
-/

open PowerSeries

/-- The formal logarithmic derivative is the inverse of 1+X. -/
theorem one_add_X_mul_derivative_log :
    (1 + X : PowerSeries ℚ) * derivative (log ℚ) = 1 := by
  simpa only [mul_comm] using (derivative_log_mul_one_add_X (A := ℚ))

/-- Multiplying the logarithmic derivative of f by f recovers f'. -/
theorem mul_derivative_logOf (f : PowerSeries ℚ) (hf : constantCoeff f = 1) :
    f * derivative (logOf f) = derivative f := by
  have hs : HasSubst (f - 1) :=
    HasSubst.of_constantCoeff_zero' (by simp [hf])
  have hunit := congrArg (substAlgHom hs) one_add_X_mul_derivative_log
  have hnorm : f * (derivative (log ℚ)).subst (f - 1) = 1 := by
    have hcancel : (1 : PowerSeries ℚ) + (f - 1) = f := by ring
    simpa only [map_mul, map_add, map_one, substAlgHom_X, hcancel,
      coe_substAlgHom] using hunit
  rw [logOf_eq, derivative_subst hs]
  simp only [map_sub, derivative_one, sub_zero]
  rw [← mul_assoc, hnorm, one_mul]

/-- The formal logarithm is additive on products with constant term one. -/
theorem logOf_mul (f g : PowerSeries ℚ)
    (hf : constantCoeff f = 1) (hg : constantCoeff g = 1) :
    logOf (f * g) = logOf f + logOf g := by
  have hfg : constantCoeff (f * g) = 1 := by simp [hf, hg]
  have hu : IsUnit (f * g) := isUnit_iff_constantCoeff.mpr (by simp [hfg])
  apply derivative.ext
  · apply hu.mul_left_cancel
    rw [mul_derivative_logOf _ hfg, map_add, mul_add]
    have hleft : f * g * derivative (logOf f) = g * derivative f := by
      rw [mul_right_comm, mul_derivative_logOf f hf, mul_comm]
    have hright : f * g * derivative (logOf g) = f * derivative g := by
      rw [mul_assoc, mul_derivative_logOf g hg]
    rw [hleft, hright]
    simp only [Derivation.leibniz, smul_eq_mul]
    ring
  · simp [constantCoeff_logOf hf, constantCoeff_logOf hg, constantCoeff_logOf hfg]

/-- The formal power identity underlying φ(t)=pt. -/
theorem logOf_pow (f : PowerSeries ℚ) (hf : constantCoeff f = 1) (n : ℕ) :
    logOf (f ^ n) = n • logOf f := by
  induction n with
  | zero => simp [logOf_eq]
  | succ n ih =>
    rw [pow_succ, logOf_mul _ _ (by simp [hf]) hf, ih, succ_nsmul]

theorem log_subst_one_add_X_pow (n : ℕ) :
    (log ℚ).subst ((1 + X : PowerSeries ℚ) ^ n - 1) = n • log ℚ := by
  change logOf ((1 + X : PowerSeries ℚ) ^ n) = _
  rw [logOf_pow _ (by simp), logOf_one_add_X]

theorem coeff_pow_eq_zero_of_lt (g : PowerSeries ℚ)
    (hg : constantCoeff g = 0) {m d : ℕ} (hd : d < m) : coeff d (g ^ m) = 0 := by
  apply coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast hd) (le_order_pow_of_constantCoeff_eq_zero m hg)

/-- Substitution has a finite coefficient formula when the constant term is zero. -/
theorem coeff_subst_log (g : PowerSeries ℚ) (hg : constantCoeff g = 0) (d : ℕ) :
    coeff d ((log ℚ).subst g) =
      ∑ m ∈ Finset.range (d + 1), coeff m (log ℚ) * coeff d (g ^ m) := by
  rw [coeff_subst' (HasSubst.of_constantCoeff_zero' hg)]
  simp only [smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro m hm
  by_contra hnot
  have hdm : d < m := by
    have hge : d + 1 ≤ m := Nat.le_of_not_gt (by simpa using hnot)
    omega
  apply hm
  change coeff m (log ℚ) * coeff d (g ^ m) = 0
  rw [coeff_pow_eq_zero_of_lt g hg hdm, mul_zero]

/-- The logarithm has integral coefficients when expressed in the divided-power basis. -/
def integralLogCoeff (d : ℕ) : ℤ :=
  if d = 0 then 0 else (-1) ^ (d + 1) * (d - 1).factorial

theorem integralLogCoeff_eq (d : ℕ) :
    (integralLogCoeff d : ℚ) = (d.factorial : ℚ) * coeff d (log ℚ) := by
  cases d with
  | zero => simp [integralLogCoeff]
  | succ d =>
    simp only [integralLogCoeff, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel,
      Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast,
      coeff_log, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Algebra.algebraMap_self, RingHom.id_apply]
    field_simp

theorem polynomial_coeff_pow_eq_zero (g : Polynomial ℤ) (hg : g.coeff 0 = 0)
    {m d : ℕ} (hd : d < m) : (g ^ m).coeff d = 0 :=
  Polynomial.X_pow_dvd_iff.mp (pow_dvd_pow_of_dvd (Polynomial.X_dvd_iff.mpr hg) m) d hd

/-- The integral matrix of substitution on the divided-power polynomial basis. -/
def dividedSubstCoeff (g : Polynomial ℤ) (m d : ℕ) : ℤ :=
  (d.factorial / m.factorial : ℕ) * (g ^ m).coeff d

theorem dividedSubstCoeff_eq (g : Polynomial ℤ) (hg : g.coeff 0 = 0) (m d : ℕ) :
    (dividedSubstCoeff g m d : ℚ) / (d.factorial : ℚ) =
      (((g ^ m).coeff d : ℤ) : ℚ) / (m.factorial : ℚ) := by
  by_cases hmd : m ≤ d
  · have hdiv := Nat.factorial_dvd_factorial hmd
    have hm : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    have hd : (d.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
    simp only [dividedSubstCoeff, Int.cast_mul, Int.cast_natCast]
    rw [Nat.cast_div hdiv (by exact_mod_cast Nat.factorial_ne_zero m)]
    field_simp
  · rw [polynomial_coeff_pow_eq_zero g hg (Nat.lt_of_not_ge hmd)]
    simp [dividedSubstCoeff, polynomial_coeff_pow_eq_zero g hg (Nat.lt_of_not_ge hmd)]

def ratSeries (g : Polynomial ℤ) : PowerSeries ℚ :=
  (g.map (Int.castRingHom ℚ) : Polynomial ℚ)

@[simp]
theorem ratSeries_coeff (g : Polynomial ℤ) (d : ℕ) :
    coeff d (ratSeries g) = (g.coeff d : ℚ) := by
  simp [ratSeries]

@[simp]
theorem ratSeries_pow (g : Polynomial ℤ) (m : ℕ) :
    ratSeries (g ^ m) = ratSeries g ^ m := by
  simp [ratSeries]

/-- Substitution on the divided-power coefficients is genuinely integral. -/
theorem integral_subst_log_coeff (g : Polynomial ℤ) (hg : g.coeff 0 = 0) (d : ℕ) :
    (d.factorial : ℚ) * coeff d ((log ℚ).subst (ratSeries g)) =
      ((∑ m ∈ Finset.range (d + 1), integralLogCoeff m * dividedSubstCoeff g m d : ℤ) : ℚ) := by
  have hg' : constantCoeff (ratSeries g) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, ratSeries_coeff, hg, Int.cast_zero]
  rw [coeff_subst_log _ hg', Finset.mul_sum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Int.cast_mul, integralLogCoeff_eq, ← ratSeries_pow, ratSeries_coeff]
  have hm : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hd : (d.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have he := (div_eq_iff hd).mp (dividedSubstCoeff_eq g hg m d)
  rw [he]
  field_simp

def powerSubstitution (n : ℕ) : Polynomial ℤ := (1 + Polynomial.X) ^ n - 1

@[simp]
theorem powerSubstitution_zero (n : ℕ) : (powerSubstitution n).coeff 0 = 0 := by
  simp [powerSubstitution, Polynomial.coeff_zero_eq_eval_zero]

@[simp]
theorem ratSeries_powerSubstitution (n : ℕ) :
    ratSeries (powerSubstitution n) = (1 + X : PowerSeries ℚ) ^ n - 1 := by
  simp [ratSeries, powerSubstitution]

/-- Integer coefficient identity for log((1+X)^n)=n log(1+X). -/
theorem integral_log_power_coeff (n d : ℕ) :
    ∑ m ∈ Finset.range (d + 1),
      integralLogCoeff m * dividedSubstCoeff (powerSubstitution n) m d =
        (n : ℤ) * integralLogCoeff d := by
  apply Int.cast_injective (α := ℚ)
  rw [← integral_subst_log_coeff _ (powerSubstitution_zero n), ratSeries_powerSubstitution,
    log_subst_one_add_X_pow, map_nsmul, nsmul_eq_mul, Int.cast_mul,
    Int.cast_natCast, integralLogCoeff_eq]
  ring

/-- High divided-power logarithm coefficients vanish modulo any fixed p-power. -/
theorem integralLogCoeff_mod_eq_zero (p : ℕ) [Fact p.Prime]
    (k d : ℕ) (hd : p * k < d) :
    (integralLogCoeff d : ZMod (p ^ k)) = 0 := by
  have hd0 : d ≠ 0 := by omega
  have hfact : p ^ k ∣ (d - 1).factorial :=
    (PeriodRings.pow_dvd_factorial_multiple p k).trans
      (Nat.factorial_dvd_factorial (by omega))
  have hz := (ZMod.natCast_eq_zero_iff (d - 1).factorial (p ^ k)).mpr hfact
  simp only [integralLogCoeff, ite_eq_right hd0, Int.cast_mul, Int.cast_natCast, hz, mul_zero]

def truncatedLogCoeff (g : Polynomial ℤ) (N d : ℕ) : ℤ :=
  ∑ m ∈ Finset.range (N + 1), integralLogCoeff m * dividedSubstCoeff g m d

/-- The finite logarithm truncations satisfy the power identity modulo p^k
in every divided-power coefficient, uniformly in the output degree. -/
theorem truncated_log_power_mod (p : ℕ) [Fact p.Prime] (k n d : ℕ) :
    (truncatedLogCoeff (powerSubstitution n) (p * k) d : ZMod (p ^ k)) =
      (n : ZMod (p ^ k)) *
        (if d ≤ p * k then (integralLogCoeff d : ZMod (p ^ k)) else 0) := by
  let a : ℕ → ZMod (p ^ k) := fun m =>
    (integralLogCoeff m : ZMod (p ^ k)) * dividedSubstCoeff (powerSubstitution n) m d
  have hlarge (m : ℕ) (hm : p * k < m) : a m = 0 := by
    dsimp only [a]
    rw [integralLogCoeff_mod_eq_zero p k m hm, zero_mul]
  have hdegree (m : ℕ) (hm : d < m) : a m = 0 := by
    simp [a, dividedSubstCoeff,
      polynomial_coeff_pow_eq_zero _ (powerSubstitution_zero n) hm]
  have hfirst : ∑ m ∈ Finset.range (p * k + 1), a m =
      ∑ m ∈ Finset.range (max (p * k) d + 1), a m := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro m _ hm
    apply hlarge
    simp only [Finset.mem_range] at hm
    omega
  have hsecond : ∑ m ∈ Finset.range (d + 1), a m =
      ∑ m ∈ Finset.range (max (p * k) d + 1), a m := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro m _ hm
    apply hdegree
    simp only [Finset.mem_range] at hm
    omega
  have hfull : ∑ m ∈ Finset.range (d + 1), a m =
      (n : ZMod (p ^ k)) * (integralLogCoeff d : ZMod (p ^ k)) := by
    simpa only [a, Int.cast_sum, Int.cast_mul, Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ZMod (p ^ k))) (integral_log_power_coeff n d)
  simp only [truncatedLogCoeff, Int.cast_sum, Int.cast_mul]
  change (∑ m ∈ Finset.range (p * k + 1), a m) = _
  rw [hfirst, ← hsecond, hfull]
  by_cases hd : d ≤ p * k
  · rw [ite_eq_left hd]
  · rw [ite_eq_right hd, integralLogCoeff_mod_eq_zero p k d (Nat.lt_of_not_ge hd)]

/-- A finite logarithm substitution, in the ordinary rational polynomial ring. -/
def partialLogPolynomial (g : Polynomial ℤ) (N : ℕ) : Polynomial ℚ :=
  ∑ m ∈ Finset.range (N + 1),
    Polynomial.C ((integralLogCoeff m : ℚ) / (m.factorial : ℚ)) *
      (g.map (Int.castRingHom ℚ)) ^ m

theorem partialLogPolynomial_coeff (g : Polynomial ℤ) (hg : g.coeff 0 = 0)
    (N d : ℕ) :
    (d.factorial : ℚ) * (partialLogPolynomial g N).coeff d =
      (truncatedLogCoeff g N d : ℚ) := by
  simp only [partialLogPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, ← Polynomial.map_pow, Polynomial.coeff_map,
    Int.coe_castRingHom, truncatedLogCoeff, Int.cast_sum, Int.cast_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  have hd : (d.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have he := (div_eq_iff hd).mp (dividedSubstCoeff_eq g hg m d)
  rw [he]
  ring

@[simp]
theorem dividedSubstCoeff_X (m d : ℕ) :
    dividedSubstCoeff Polynomial.X m d = if d = m then 1 else 0 := by
  simp only [dividedSubstCoeff, Polynomial.coeff_X_pow]
  split_ifs with h
  · subst d
    simp only [mul_one]
    exact_mod_cast Nat.div_self (Nat.factorial_pos m)
  · simp

theorem truncatedLogCoeff_X (N d : ℕ) :
    truncatedLogCoeff Polynomial.X N d =
      if d ≤ N then integralLogCoeff d else 0 := by
  simp [truncatedLogCoeff, dividedSubstCoeff_X, mul_ite, Finset.mem_range]

/-- The error in the finite power identity, with integral divided-power coefficients. -/
def logPowerErrorCoeff (n N d : ℕ) : ℤ :=
  truncatedLogCoeff (powerSubstitution n) N d -
    (n : ℤ) * (if d ≤ N then integralLogCoeff d else 0)

def logPowerError (n N : ℕ) : Polynomial ℚ :=
  partialLogPolynomial (powerSubstitution n) N -
    Polynomial.C (n : ℚ) * partialLogPolynomial Polynomial.X N

theorem logPowerError_coeff (n N d : ℕ) :
    (d.factorial : ℚ) * (logPowerError n N).coeff d =
      (logPowerErrorCoeff n N d : ℚ) := by
  simp only [logPowerError, Polynomial.coeff_sub, Polynomial.coeff_C_mul, mul_sub]
  rw [partialLogPolynomial_coeff _ (powerSubstitution_zero n), mul_left_comm,
    partialLogPolynomial_coeff _ (by simp), truncatedLogCoeff_X]
  simp only [logPowerErrorCoeff, Int.cast_sub, Int.cast_mul, Int.cast_natCast]

theorem logPowerErrorCoeff_dvd (p : ℕ) [Fact p.Prime] (k n d : ℕ) :
    (p ^ k : ℤ) ∣ logPowerErrorCoeff n (p * k) d := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
  simpa only [logPowerErrorCoeff, Int.cast_sub, Int.cast_mul, Int.cast_natCast,
    Int.cast_ite, Int.cast_zero, sub_eq_zero] using truncated_log_power_mod p k n d

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings

variable (p : ℕ) [Fact p.Prime]

/-- The finite logarithm in the integral crystalline envelope. -/
def integralLogPartial (x : PeriodRings.AInf p) (hx : PeriodRings.thetaModP p x = 0) (N : ℕ) :
    PeriodRings.ACrisUncompleted p :=
  ∑ m ∈ Finset.range (N + 1),
    (integralLogCoeff m : PeriodRings.ACrisUncompleted p) * PeriodRings.dividedPower p x m hx

@[simp]
theorem integralLogCoeff_succ (m : ℕ) :
    integralLogCoeff (m + 1) = (-1) ^ m * m.factorial := by
  simp [integralLogCoeff, pow_add]

theorem integralLogPartial_eq (x : PeriodRings.AInf p) (hx : PeriodRings.thetaModP p x = 0) (N : ℕ) :
    integralLogPartial p x hx N =
      ∑ m ∈ Finset.range N, PeriodRings.crystallineLogTerm p x hx m := by
  rw [integralLogPartial, Finset.sum_range_succ']
  have hzero : integralLogCoeff 0 = 0 := rfl
  simp only [hzero, Int.cast_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro m _
  simp only [integralLogCoeff_succ, Int.cast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one, Int.cast_natCast, PeriodRings.crystallineLogTerm]

theorem partialLogPolynomial_eval (g : Polynomial ℤ) (N : ℕ) (x y : PeriodRings.AInf p)
    (hy : PeriodRings.thetaModP p y = 0)
    (he : (g.map (Int.castRingHom ℚ)).eval₂ (algebraMap ℚ (PeriodRings.AInfFractionField p))
      (algebraMap (PeriodRings.AInf p) (PeriodRings.AInfFractionField p) x) =
        algebraMap (PeriodRings.AInf p) (PeriodRings.AInfFractionField p) y) :
    (partialLogPolynomial g N).eval₂ (algebraMap ℚ (PeriodRings.AInfFractionField p))
      (algebraMap (PeriodRings.AInf p) (PeriodRings.AInfFractionField p) x) =
        (integralLogPartial p y hy N : PeriodRings.AInfFractionField p) := by
  change _ = (PeriodRings.aCrisUncompleted p).val (∑ m ∈ Finset.range (N + 1),
    (integralLogCoeff m : PeriodRings.ACrisUncompleted p) * PeriodRings.dividedPower p y m hy)
  simp only [partialLogPolynomial, Polynomial.eval₂_finsetSum, Polynomial.eval₂_mul,
    Polynomial.eval₂_C, Polynomial.eval₂_pow, he, map_div₀, map_intCast, map_natCast,
    map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro m _
  change (integralLogCoeff m : PeriodRings.AInfFractionField p) / (m.factorial : PeriodRings.AInfFractionField p) *
      algebraMap (PeriodRings.AInf p) (PeriodRings.AInfFractionField p) y ^ m =
    (integralLogCoeff m : PeriodRings.AInfFractionField p) *
      (algebraMap (PeriodRings.AInf p) (PeriodRings.AInfFractionField p) y ^ m / (m.factorial : PeriodRings.AInfFractionField p))
  ring

/-- An integral divided-power expansion realizes the corresponding rational polynomial. -/
theorem dividedPolynomial_eval (q : Polynomial ℚ) (b : ℕ → ℤ)
    (hb : ∀ d, (d.factorial : ℚ) * q.coeff d = (b d : ℚ))
    (x : PeriodRings.AInf p) (hx : PeriodRings.thetaModP p x = 0) :
    q.eval₂ (algebraMap ℚ (PeriodRings.AInfFractionField p))
      (algebraMap (PeriodRings.AInf p) (PeriodRings.AInfFractionField p) x) =
    ((∑ d ∈ q.support, (b d : PeriodRings.ACrisUncompleted p) * PeriodRings.dividedPower p x d hx :
      PeriodRings.ACrisUncompleted p) : PeriodRings.AInfFractionField p) := by
  change _ = (PeriodRings.aCrisUncompleted p).val _
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  have hd : (d.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hc : q.coeff d = (b d : ℚ) / (d.factorial : ℚ) := by
    apply (eq_div_iff hd).mpr
    simpa only [mul_comm] using hb d
  rw [hc, map_div₀, map_intCast, map_natCast, map_mul, map_intCast]
  change (b d : PeriodRings.AInfFractionField p) / (d.factorial : PeriodRings.AInfFractionField p) *
      algebraMap (PeriodRings.AInf p) (PeriodRings.AInfFractionField p) x ^ d =
    (b d : PeriodRings.AInfFractionField p) *
      (algebraMap (PeriodRings.AInf p) (PeriodRings.AInfFractionField p) x ^ d / (d.factorial : PeriodRings.AInfFractionField p))
  ring

/-- Coefficient divisibility gives ideal membership for a divided-power polynomial. -/
theorem dividedPolynomial_mem (q : Polynomial ℚ) (b : ℕ → ℤ) (k : ℕ)
    (hb : ∀ d, (p ^ k : ℤ) ∣ b d) (x : PeriodRings.AInf p) (hx : PeriodRings.thetaModP p x = 0) :
    (∑ d ∈ q.support, (b d : PeriodRings.ACrisUncompleted p) * PeriodRings.dividedPower p x d hx) ∈
      (Ideal.span {(p : PeriodRings.ACrisUncompleted p)}) ^ k := by
  apply Ideal.sum_mem
  intro d _
  apply Ideal.mul_mem_right
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  obtain ⟨c, hc⟩ := hb d
  refine ⟨(c : PeriodRings.ACrisUncompleted p), ?_⟩
  simpa only [Int.cast_mul, Int.cast_pow, Int.cast_natCast] using
    congrArg (fun z : ℤ => (z : PeriodRings.ACrisUncompleted p)) hc

theorem powerDifference_kernel (x : PeriodRings.AInf p) (hx : PeriodRings.thetaModP p x = 0) (n : ℕ) :
    PeriodRings.thetaModP p ((1 + x) ^ n - 1) = 0 := by
  simp [hx]

theorem powerSubstitution_eval (x : PeriodRings.AInf p) (n : ℕ) :
    ((powerSubstitution n).map (Int.castRingHom ℚ)).eval₂
      (algebraMap ℚ (PeriodRings.AInfFractionField p)) (algebraMap (PeriodRings.AInf p) (PeriodRings.AInfFractionField p) x) =
      algebraMap (PeriodRings.AInf p) (PeriodRings.AInfFractionField p) ((1 + x) ^ n - 1) := by
  simp [powerSubstitution]

/-- The error between finite logarithm sums lies in the required p-power ideal. -/
theorem integralLogPartial_power_mem (x : PeriodRings.AInf p) (hx : PeriodRings.thetaModP p x = 0)
    (k n : ℕ) :
    integralLogPartial p ((1 + x) ^ n - 1) (powerDifference_kernel p x hx n) (p * k) -
      (n : PeriodRings.ACrisUncompleted p) * integralLogPartial p x hx (p * k) ∈
      (Ideal.span {(p : PeriodRings.ACrisUncompleted p)}) ^ k := by
  have heval :
      (logPowerError n (p * k)).eval₂ (algebraMap ℚ (PeriodRings.AInfFractionField p))
        (algebraMap (PeriodRings.AInf p) (PeriodRings.AInfFractionField p) x) =
      ((integralLogPartial p ((1 + x) ^ n - 1) (powerDifference_kernel p x hx n) (p * k) -
        (n : PeriodRings.ACrisUncompleted p) * integralLogPartial p x hx (p * k) :
          PeriodRings.ACrisUncompleted p) : PeriodRings.AInfFractionField p) := by
    rw [logPowerError, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      map_natCast, partialLogPolynomial_eval p _ _ x _ _ (powerSubstitution_eval p x n),
      partialLogPolynomial_eval p Polynomial.X _ x x hx (by simp)]
    rfl
  have heq :
      integralLogPartial p ((1 + x) ^ n - 1) (powerDifference_kernel p x hx n) (p * k) -
        (n : PeriodRings.ACrisUncompleted p) * integralLogPartial p x hx (p * k) =
      ∑ d ∈ (logPowerError n (p * k)).support,
        (logPowerErrorCoeff n (p * k) d : PeriodRings.ACrisUncompleted p) * PeriodRings.dividedPower p x d hx := by
    apply Subtype.ext
    rw [← dividedPolynomial_eval p _ _ (logPowerError_coeff n (p * k)) x hx]
    exact heval.symm
  rw [heq]
  exact dividedPolynomial_mem p _ _ k (logPowerErrorCoeff_dvd p k n) x hx

/-- The power identity for the constructed logarithm in the actual A_cris. -/
theorem crystallineLog_power (x : PeriodRings.AInf p) (hx : PeriodRings.thetaModP p x = 0) (n : ℕ) :
    PeriodRings.crystallineLog p ((1 + x) ^ n - 1) (powerDifference_kernel p x hx n) =
      (n : PeriodRings.ACris p) * PeriodRings.crystallineLog p x hx := by
  apply AdicCompletion.ext_evalₐ
  intro k
  rw [PeriodRings.crystallineLog_mod, map_mul, map_natCast, PeriodRings.crystallineLog_mod]
  rw [← integralLogPartial_eq, ← integralLogPartial_eq]
  change Ideal.Quotient.mk _ _ =
    Ideal.Quotient.mk _ ((n : PeriodRings.ACrisUncompleted p) * integralLogPartial p x hx (p * k))
  exact Ideal.Quotient.eq.mpr (integralLogPartial_power_mem p x hx k n)

/-- Frobenius acts on the actual cyclotomic logarithm by multiplication by p. -/
theorem frobenius_cyclotomicPeriod :
    PeriodRings.aCrisFrobenius p (PeriodRings.cyclotomicPeriod p) = (p : PeriodRings.ACris p) * PeriodRings.cyclotomicPeriod p := by
  rw [PeriodRings.cyclotomicPeriod, PeriodRings.frobenius_crystallineLog]
  convert crystallineLog_power p (PeriodRings.cyclotomicDifference p)
    (PeriodRings.cyclotomicDifference_thetaModP p) p using 1
  congr 1
  exact PeriodRings.frobenius_cyclotomicDifference p

theorem bCrisPlusFrobenius_cyclotomicPeriod :
    PeriodRings.bCrisPlusFrobenius p (algebraMap (PeriodRings.ACris p) (PeriodRings.BCrisPlus p) (PeriodRings.cyclotomicPeriod p)) =
      (p : PeriodRings.BCrisPlus p) * algebraMap (PeriodRings.ACris p) (PeriodRings.BCrisPlus p) (PeriodRings.cyclotomicPeriod p) := by
  rw [PeriodRings.bCrisPlusFrobenius_algebraMap, frobenius_cyclotomicPeriod, map_mul, map_natCast]

theorem frobenius_period_isUnit :
    IsUnit (((algebraMap (PeriodRings.BCrisPlus p) (PeriodRings.BCris p)).comp (PeriodRings.bCrisPlusFrobenius p))
      (algebraMap (PeriodRings.ACris p) (PeriodRings.BCrisPlus p) (PeriodRings.cyclotomicPeriod p))) := by
  rw [RingHom.comp_apply, bCrisPlusFrobenius_cyclotomicPeriod, map_mul]
  simpa only [map_natCast] using
    ((IsLocalization.Away.algebraMap_isUnit (p : PeriodRings.ACris p)).map
      (algebraMap (PeriodRings.BCrisPlus p) (PeriodRings.BCris p))).mul
        (IsLocalization.Away.algebraMap_isUnit
          (algebraMap (PeriodRings.ACris p) (PeriodRings.BCrisPlus p) (PeriodRings.cyclotomicPeriod p)))

/-- Frobenius on B_cris, justified by the proved cyclotomic-period identity. -/
def bCrisFrobenius : PeriodRings.BCris p →+* PeriodRings.BCris p :=
  Localization.awayLift
    ((algebraMap (PeriodRings.BCrisPlus p) (PeriodRings.BCris p)).comp (PeriodRings.bCrisPlusFrobenius p))
    (algebraMap (PeriodRings.ACris p) (PeriodRings.BCrisPlus p) (PeriodRings.cyclotomicPeriod p)) (frobenius_period_isUnit p)

theorem bCrisFrobenius_algebraMap (x : PeriodRings.BCrisPlus p) :
    bCrisFrobenius p (algebraMap (PeriodRings.BCrisPlus p) (PeriodRings.BCris p) x) =
      algebraMap (PeriodRings.BCrisPlus p) (PeriodRings.BCris p) (PeriodRings.bCrisPlusFrobenius p x) := by
  exact IsLocalization.Away.lift_eq _ (frobenius_period_isUnit p) x

end NumberTheory.PadicHodge.WeakAdmissibility.Logarithm

end

end OAI
