import OAI.NumberTheory.Quaternion.Arithmetic.LocalCompletion

/-! # Prime Local Integral -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.PrimeLocalIntegral

noncomputable section

section

/-! Integer multiples stay inside the finite-place exponential disk, and
their exponentials are the corresponding group powers. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

theorem finite_norm_nsmul_le (v : HeightOneSpectrum (𝓞 F))
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace (v.adicCompletion F) E]
    (m : ℕ) (X : E) : ‖m • X‖ ≤ ‖X‖ := by
  rw [← Nat.cast_smul_eq_nsmul (v.adicCompletion F), norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg X) (LocalCompletion.natCast_norm_le_one v m)

theorem nsmul_mem_finite_expSeries_ball (v : HeightOneSpectrum (𝓞 F))
    {A : Type*} [NormedRing A] [NormedAlgebra (v.adicCompletion F) A]
    (m : ℕ) {X : A}
    (hX : X ∈ Metric.eball 0 (NormedSpace.expSeries (v.adicCompletion F) A).radius) :
    m • X ∈ Metric.eball 0 (NormedSpace.expSeries (v.adicCompletion F) A).radius := by
  have hdist : edist (m • X) 0 ≤ edist X 0 := by
    simpa only [edist_dist, dist_zero_right] using
      ENNReal.ofReal_le_ofReal (finite_norm_nsmul_le v m X)
  exact hdist.trans_lt hX

theorem finite_exp_nsmul (v : HeightOneSpectrum (𝓞 F))
    {A : Type*} [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A]
    (m : ℕ) {X : A}
    (hX : X ∈ Metric.eball 0 (NormedSpace.expSeries (v.adicCompletion F) A).radius) :
    NormedSpace.exp (m • X) = (NormedSpace.exp X) ^ m := by
  let : CharZero (v.adicCompletion F) := Algebra.charZero_of_charZero F (v.adicCompletion F)
  induction m with
  | zero => simp
  | succ m hm =>
    rw [succ_nsmul, NormedSpace.exp_add_of_commute_of_mem_ball
      ((Commute.refl X).smul_left m) (nsmul_mem_finite_expSeries_ball v m hX) hX, hm, pow_succ]

end

section

/-! Closed multiplicative subgroups contain the local exponential family
obtained by completing the nonnegative integer powers of one element. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology

variable {F : Type} [Field F] [NumberField F]

def integralPrimeScalars (v : HeightOneSpectrum (𝓞 F)) : Set (v.adicCompletion F) :=
  closure (range (fun m : ℕ => (m : v.adicCompletion F)))

theorem norm_le_one_of_mem_integralPrimeScalars (v : HeightOneSpectrum (𝓞 F))
    {t : v.adicCompletion F} (ht : t ∈ integralPrimeScalars v) : ‖t‖ ≤ 1 := by
  apply closure_minimal _ (isClosed_le continuous_norm continuous_const) ht
  rintro _ ⟨m, rfl⟩
  exact LocalCompletion.natCast_norm_le_one v m

theorem smul_mem_finite_expSeries_ball (v : HeightOneSpectrum (𝓞 F))
    {A : Type*} [NormedRing A] [NormedAlgebra (v.adicCompletion F) A]
    {X : A} (hX : X ∈ Metric.eball 0 (NormedSpace.expSeries (v.adicCompletion F) A).radius)
    {t : v.adicCompletion F} (ht : ‖t‖ ≤ 1) :
    t • X ∈ Metric.eball 0 (NormedSpace.expSeries (v.adicCompletion F) A).radius := by
  have hnorm : ‖t • X‖ ≤ ‖X‖ := by
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg X) ht
  have hdist : edist (t • X) 0 ≤ edist X 0 := by
    simpa only [edist_dist, dist_zero_right] using ENNReal.ofReal_le_ofReal hnorm
  exact hdist.trans_lt hX

theorem finite_exp_smul_mem_closed_submonoid (v : HeightOneSpectrum (𝓞 F))
    {A : Type*} [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A]
    (H : Submonoid A) (hclosed : IsClosed (H : Set A))
    {X : A} (hX : X ∈ Metric.eball 0 (NormedSpace.expSeries (v.adicCompletion F) A).radius)
    (hexp : NormedSpace.exp X ∈ H)
    {t : v.adicCompletion F} (ht : t ∈ integralPrimeScalars v) :
    NormedSpace.exp (t • X) ∈ H := by
  let : CharZero (v.adicCompletion F) := Algebra.charZero_of_charZero F (v.adicCompletion F)
  have htx := smul_mem_finite_expSeries_ball v hX (norm_le_one_of_mem_integralPrimeScalars v ht)
  have hsmul : ContinuousAt (fun a : v.adicCompletion F => a • X) t := by fun_prop
  have hc : ContinuousAt (fun a : v.adicCompletion F => NormedSpace.exp (a • X)) t := by
    exact (NormedSpace.analyticAt_exp_of_mem_ball (t • X) htx).continuousAt.comp
      (f := fun a : v.adicCompletion F => a • X) hsmul
  obtain ⟨a, ha, hat⟩ := mem_closure_iff_seq_limit.mp ht
  apply hclosed.mem_of_tendsto (hc.tendsto.comp hat)
  apply Eventually.of_forall
  intro j
  obtain ⟨m, hm⟩ := ha j
  change NormedSpace.exp (a j • X) ∈ H
  change (m : v.adicCompletion F) = a j at hm
  rw [← hm, Nat.cast_smul_eq_nsmul, finite_exp_nsmul v m hX]
  exact H.pow_mem hexp m

end

section

/-! Completing nonnegative integer scalars at a finite place gives a
closed subring: powers of the residue prime show that -1 is a limit too. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology

variable {F : Type} [Field F] [NumberField F]

theorem neg_one_mem_integralPrimeScalars (v : HeightOneSpectrum (𝓞 F)) :
    (-1 : v.adicCompletion F) ∈ integralPrimeScalars v := by
  have hprime : ‖(LocalCompletion.residuePrime v : v.adicCompletion F)‖ < 1 :=
    (LocalCompletion.natCast_norm_lt_one_iff v _).mpr dvd_rfl
  have he : ∀ n : ℕ, ((LocalCompletion.residuePrime v ^ n - 1 : ℕ) : v.adicCompletion F) =
      (LocalCompletion.residuePrime v : v.adicCompletion F) ^ n - 1 := by
    intro n
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (LocalCompletion.residuePrime_prime v).ne_zero)),
      Nat.cast_pow, Nat.cast_one]
  have ht : Tendsto (fun n : ℕ => ((LocalCompletion.residuePrime v ^ n - 1 : ℕ) : v.adicCompletion F))
      atTop (𝓝 (-1)) := by
    simp_rw [he]
    simpa only [zero_sub] using
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hprime).sub tendsto_const_nhds
  exact mem_closure_of_tendsto ht (Eventually.of_forall fun n => mem_range_self _)

def primeScalarSemiring (v : HeightOneSpectrum (𝓞 F)) : Subsemiring (v.adicCompletion F) :=
  (⊥ : Subsemiring (v.adicCompletion F)).topologicalClosure

theorem primeScalarSemiring_coe (v : HeightOneSpectrum (𝓞 F)) :
    (primeScalarSemiring v : Set (v.adicCompletion F)) = integralPrimeScalars v := by
  simp only [primeScalarSemiring, Subsemiring.topologicalClosure_coe, Subsemiring.coe_bot,
    integralPrimeScalars]

def primeIntegralSubring (v : HeightOneSpectrum (𝓞 F)) : Subring (v.adicCompletion F) where
  carrier := primeScalarSemiring v
  zero_mem' := (primeScalarSemiring v).zero_mem
  one_mem' := (primeScalarSemiring v).one_mem
  add_mem' := (primeScalarSemiring v).add_mem
  mul_mem' := (primeScalarSemiring v).mul_mem
  neg_mem' {x} hx := by
    have hneg : (-1 : v.adicCompletion F) ∈ primeScalarSemiring v := by
      change (-1 : v.adicCompletion F) ∈ (primeScalarSemiring v : Set (v.adicCompletion F))
      rw [primeScalarSemiring_coe]
      exact neg_one_mem_integralPrimeScalars v
    change -x ∈ primeScalarSemiring v
    simpa only [neg_one_mul] using (primeScalarSemiring v).mul_mem hneg hx

theorem primeIntegralSubring_coe (v : HeightOneSpectrum (𝓞 F)) :
    (primeIntegralSubring v : Set (v.adicCompletion F)) = integralPrimeScalars v :=
  primeScalarSemiring_coe v

theorem primeIntegralSubring_isClosed (v : HeightOneSpectrum (𝓞 F)) :
    IsClosed (primeIntegralSubring v : Set (v.adicCompletion F)) :=
  (⊥ : Subsemiring (v.adicCompletion F)).isClosed_topologicalClosure

end

section

/-! Integers prime to the residue characteristic are invertible in the
completed integer scalar ring. Bézout's identity and a convergent geometric
series provide the inverse. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set Filter _root_.Topology

variable {F : Type} [Field F] [NumberField F]

theorem intCast_norm_le_one (v : HeightOneSpectrum (𝓞 F)) (z : ℤ) :
    ‖(z : v.adicCompletion F)‖ ≤ 1 := by
  rw [← norm_natAbs]
  exact LocalCompletion.natCast_norm_le_one v z.natAbs

theorem inverse_natCast_mem_primeIntegralSubring (v : HeightOneSpectrum (𝓞 F))
    (m : ℕ) (hm : ¬ LocalCompletion.residuePrime v ∣ m) :
    (m : v.adicCompletion F)⁻¹ ∈ primeIntegralSubring v := by
  have hcop : Nat.Coprime m (LocalCompletion.residuePrime v) :=
    ((LocalCompletion.residuePrime_prime v).coprime_iff_not_dvd.mpr hm).symm
  let z := Nat.gcdA m (LocalCompletion.residuePrime v)
  let y := Nat.gcdB m (LocalCompletion.residuePrime v)
  have hbez : (1 : v.adicCompletion F) = (m : v.adicCompletion F) * (z : v.adicCompletion F) +
      (LocalCompletion.residuePrime v : v.adicCompletion F) * (y : v.adicCompletion F) := by
    have h := congrArg (Int.castRingHom (v.adicCompletion F)) (Nat.gcd_eq_gcd_ab m (LocalCompletion.residuePrime v))
    simpa only [map_add, map_mul, Int.coe_castRingHom, Int.cast_natCast, hcop.gcd_eq_one,
      Nat.cast_one, Int.cast_one, z, y] using h
  let t : v.adicCompletion F := 1 - (m : v.adicCompletion F) * (z : v.adicCompletion F)
  have hteq : t = (LocalCompletion.residuePrime v : v.adicCompletion F) * (y : v.adicCompletion F) := by
    dsimp only [t]
    linear_combination hbez
  have ht : ‖t‖ < 1 := by
    rw [hteq, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (intCast_norm_le_one v y)).trans_lt
      ((LocalCompletion.natCast_norm_lt_one_iff v _).mpr dvd_rfl)
  have htR : t ∈ primeIntegralSubring v :=
    (primeIntegralSubring v).sub_mem (primeIntegralSubring v).one_mem
      ((primeIntegralSubring v).mul_mem (natCast_mem (primeIntegralSubring v) m)
        (intCast_mem (primeIntegralSubring v) z))
  have htinv : (1 - t)⁻¹ ∈ primeIntegralSubring v := by
    apply (primeIntegralSubring_isClosed v).mem_of_tendsto (hasSum_geometric_of_norm_lt_one ht)
    exact Eventually.of_forall fun s => (primeIntegralSubring v).sum_mem
      (fun j _ => (primeIntegralSubring v).pow_mem htR j)
  have hz : (z : v.adicCompletion F) ≠ 0 := by
    intro hz
    have he : t = 1 := by simp [t, hz]
    rw [he, norm_one] at ht
    exact (lt_irrefl 1) ht
  have he : (m : v.adicCompletion F)⁻¹ = (z : v.adicCompletion F) * (1 - t)⁻¹ := by
    dsimp only [t]
    rw [sub_sub_cancel, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hz, one_mul]
  rw [he]
  exact (primeIntegralSubring v).mul_mem (intCast_mem (primeIntegralSubring v) z) htinv

end

section

/-! A rational scalar of norm at most one belongs to the completed
integer ring at the finite place. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

theorem residuePrime_not_dvd_den_of_ratCast_norm_le_one
    (v : HeightOneSpectrum (𝓞 F)) (q : ℚ) (hq : ‖(q : v.adicCompletion F)‖ ≤ 1) :
    ¬ LocalCompletion.residuePrime v ∣ q.den := by
  let : CharZero (v.adicCompletion F) := Algebra.charZero_of_charZero F (v.adicCompletion F)
  intro hden
  have hnum : ¬ LocalCompletion.residuePrime v ∣ q.num.natAbs := by
    intro hnum
    have h := Nat.dvd_gcd hnum hden
    rw [q.reduced.gcd_eq_one] at h
    exact (LocalCompletion.residuePrime_prime v).ne_one (Nat.dvd_one.mp h)
  have hnumNorm : ‖(q.num : v.adicCompletion F)‖ = 1 := by
    rw [← norm_natAbs]
    exact LocalCompletion.natCast_norm_eq_one_of_not_dvd v _ hnum
  have hdenNorm : ‖(q.den : v.adicCompletion F)‖ < 1 := (LocalCompletion.natCast_norm_lt_one_iff v _).mpr hden
  have hdenPos : 0 < ‖(q.den : v.adicCompletion F)‖ :=
    norm_pos_iff.mpr (Nat.cast_ne_zero.mpr q.den_nz)
  have hgt : 1 < ‖(q : v.adicCompletion F)‖ := by
    rw [Rat.cast_def, norm_div, hnumNorm]
    exact (one_lt_div hdenPos).mpr hdenNorm
  exact (not_lt_of_ge hq) hgt

theorem ratCast_mem_primeIntegralSubring_of_norm_le_one
    (v : HeightOneSpectrum (𝓞 F)) (q : ℚ) (hq : ‖(q : v.adicCompletion F)‖ ≤ 1) :
    (q : v.adicCompletion F) ∈ primeIntegralSubring v := by
  rw [Rat.cast_def, div_eq_mul_inv]
  exact (primeIntegralSubring v).mul_mem (intCast_mem (primeIntegralSubring v) q.num)
    (inverse_natCast_mem_primeIntegralSubring v q.den
      (residuePrime_not_dvd_den_of_ratCast_norm_le_one v q hq))

end

/-! The completed integer scalars form a compact open ring in the closed
prime field, and are precisely its elements of norm at most one. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Set _root_.Topology

theorem bot_subfield_coe_eq_ratRange {K : Type*} [Field K] [CharZero K] :
    ((⊥ : Subfield K) : Set K) = range (fun q : ℚ => (q : K)) := by
  have he : (⊥ : Subfield K) = (Rat.castHom K).fieldRange := by
    apply le_antisymm bot_le
    rintro _ ⟨q, rfl⟩
    exact SubfieldClass.ratCast_mem (⊥ : Subfield K) q
  rw [he, RingHom.coe_fieldRange]
  rfl

variable {F : Type} [Field F] [NumberField F]

def primeIntegerRing (v : HeightOneSpectrum (𝓞 F)) :
    Subring (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) :=
  (primeIntegralSubring v).comap (TangentBracket.closedPrimeSubfield (v.adicCompletion F)).subtype

theorem finite_unitBall_isOpen (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen {x : v.adicCompletion F | ‖x‖ ≤ 1} := by
  have he : {x : v.adicCompletion F | ‖x‖ ≤ 1} =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    ext x
    exact Valued.toNormedField.norm_le_one_iff
  rw [he]
  exact Valued.isOpen_valuationSubring (v.adicCompletion F)

theorem mem_primeIntegerRing_iff (v : HeightOneSpectrum (𝓞 F))
    (x : TangentBracket.closedPrimeSubfield (v.adicCompletion F)) :
    x ∈ primeIntegerRing v ↔ ‖x‖ ≤ 1 := by
  constructor
  · intro hx
    apply norm_le_one_of_mem_integralPrimeScalars v
    rw [← primeIntegralSubring_coe]
    exact hx
  · intro hx
    let : CharZero (v.adicCompletion F) := Algebra.charZero_of_charZero F (v.adicCompletion F)
    have hxRat : x.val ∈ closure (range (fun q : ℚ => (q : v.adicCompletion F))) := by
      have h := x.property
      change x.val ∈ closure ((⊥ : Subfield (v.adicCompletion F)) : Set (v.adicCompletion F)) at h
      rwa [bot_subfield_coe_eq_ratRange] at h
    change x.val ∈ (primeIntegralSubring v : Set (v.adicCompletion F))
    rw [← (primeIntegralSubring_isClosed v).closure_eq]
    apply mem_closure_iff.mpr
    intro U hU hxU
    obtain ⟨y, hy, hRat⟩ := mem_closure_iff.mp hxRat
      (U ∩ {z : v.adicCompletion F | ‖z‖ ≤ 1}) (hU.inter (finite_unitBall_isOpen v)) ⟨hxU, hx⟩
    obtain ⟨q, rfl⟩ := hRat
    exact ⟨(q : v.adicCompletion F), hy.1, ratCast_mem_primeIntegralSubring_of_norm_le_one v q hy.2⟩

theorem primeIntegerRing_isOpen (v : HeightOneSpectrum (𝓞 F)) :
    IsOpen (primeIntegerRing v : Set (TangentBracket.closedPrimeSubfield (v.adicCompletion F))) := by
  have he : (primeIntegerRing v : Set (TangentBracket.closedPrimeSubfield (v.adicCompletion F))) =
      Subtype.val ⁻¹' {x : v.adicCompletion F | ‖x‖ ≤ 1} := by
    ext x
    exact mem_primeIntegerRing_iff v x
  rw [he]
  exact (finite_unitBall_isOpen v).preimage continuous_subtype_val

theorem primeIntegerRing_isCompact (v : HeightOneSpectrum (𝓞 F)) :
    IsCompact (primeIntegerRing v : Set (TangentBracket.closedPrimeSubfield (v.adicCompletion F))) := by
  have he : (primeIntegerRing v : Set (TangentBracket.closedPrimeSubfield (v.adicCompletion F))) =
      Subtype.val ⁻¹' Metric.closedBall (0 : v.adicCompletion F) 1 := by
    ext x
    change x ∈ primeIntegerRing v ↔ dist x.val 0 ≤ 1
    rw [dist_zero_right]
    exact mem_primeIntegerRing_iff v x
  rw [he]
  exact (⊥ : Subfield (v.adicCompletion F)).isClosed_topologicalClosure.isClosedEmbedding_subtypeVal
    |>.isCompact_preimage (isCompact_closedBall 0 1)

end

end OAI.NumberTheory.Quaternion.Arithmetic.PrimeLocalIntegral
