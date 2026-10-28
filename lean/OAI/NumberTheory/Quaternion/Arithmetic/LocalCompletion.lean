import OAI.NumberTheory.Quaternion.Arithmetic.TangentBracket

/-! # Local Completion -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.LocalCompletion

noncomputable section

section

/-! A number-field basis remains a finite spanning set after completion
over a complete scalar field containing the rational scalars. -/

open scoped Classical _root_.NumberField
open Set

theorem finiteDimensional_of_dense_numberField
    {F K κ : Type} [Field F] [NumberField F]
    [NormedField K] [CharZero K] [NontriviallyNormedField κ] [CharZero κ]
    [CompleteSpace κ] [NormedAlgebra κ K]
    (φ : F →+* K) (hd : DenseRange φ) : FiniteDimensional κ K := by
  let b := Module.finBasis ℚ F
  let V : Submodule κ K := Submodule.span κ (range (fun i => φ (b i)))
  let : FiniteDimensional κ V := FiniteDimensional.span_of_finite κ (finite_range _)
  have hm : ∀ a : F, φ a ∈ V := by
    intro a
    rw [← b.sum_repr a, map_sum]
    apply V.sum_mem
    intro i _
    have hb : φ (b i) ∈ V := Submodule.subset_span (mem_range_self i)
    have hs := V.smul_mem ((b.repr a i : ℚ) : κ) hb
    rw [Algebra.smul_def, map_mul, RingHom.map_rat_algebraMap]
    change (((b.repr a i : ℚ) : K) * φ (b i)) ∈ V
    simpa only [Algebra.smul_def, map_ratCast] using hs
  have hall : ∀ x : K, x ∈ V := by
    intro x
    apply closure_minimal _ V.closed_of_finiteDimensional (hd x)
    rintro _ ⟨a, rfl⟩
    exact hm a
  exact Module.Finite.of_surjective V.subtype (fun x => ⟨⟨x, hall x⟩, rfl⟩)

theorem finiteCompletion_finiteDimensional_closedPrime
    {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    FiniteDimensional (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (v.adicCompletion F) := by
  let : CharZero (v.adicCompletion F) := Algebra.charZero_of_charZero F (v.adicCompletion F)
  let : NontriviallyNormedField (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) :=
    TangentBracket.finiteClosedPrimeNontriviallyNormedField v
  exact finiteDimensional_of_dense_numberField
    (algebraMap F (v.adicCompletion F)) (v.denseRange_algebraMap F)

end

section

/-! The tangent Lie algebra over the closed prime local field. Its
underlying span keeps the dimension relevant to local openness. -/

open scoped Classical _root_.NumberField
open Set IsDedekindDomain

section

variable {F K κ : Type} [Field F] [Field K] [Field κ] [Algebra κ K]
variable [TopologicalSpace K] [IsTopologicalRing K] {n : ℕ}
variable (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K)

theorem tangentSpanOver_commutator_mem_of_conjugation_invariant
    (H : Subgroup (G.Points ι)) (W : Submodule κ (Matrix (Fin n) (Fin n) K))
    (hclosed : IsClosed (W : Set (Matrix (Fin n) (Fin n) K)))
    (hinvariant : ∀ g ∈ H, MapsTo (TangentCone.matrixConjugation G ι g)
      (W : Set (Matrix (Fin n) (Fin n) K)) (W : Set (Matrix (Fin n) (Fin n) K)))
    {X Y : Matrix (Fin n) (Fin n) K} (hX : X ∈ W)
    (hY : Y ∈ TangentBracket.matrixTangentSpanOver (κ := κ) G ι H) : Y * X - X * Y ∈ W := by
  let f : Matrix (Fin n) (Fin n) K →ₗ[κ] Matrix (Fin n) (Fin n) K :=
    { toFun Y := Y * X - X * Y
      map_add' Y Z := by simp only [Matrix.add_mul, Matrix.mul_add]; abel
      map_smul' c Y := by simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub, RingHom.id_apply] }
  have hle : TangentBracket.matrixTangentSpanOver (κ := κ) G ι H ≤ W.comap f := by
    apply Submodule.span_le.mpr
    intro Y hY
    exact TangentBracket.tangent_commutator_mem_over_of_conjugation_invariant G ι H W hclosed hinvariant hX hY
  exact hle hY

theorem matrixTangentSpanOver_preserved_by_member
    (H : Subgroup (G.Points ι)) (g : G.Points ι) (hg : g ∈ H) :
    MapsTo (TangentCone.matrixConjugation G ι g)
      (TangentBracket.matrixTangentSpanOver (κ := κ) G ι H : Set (Matrix (Fin n) (Fin n) K))
      (TangentBracket.matrixTangentSpanOver (κ := κ) G ι H : Set (Matrix (Fin n) (Fin n) K)) := by
  have he : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer hg)
  have ht := TangentBracket.matrixConjugation_mapsTo_tangentConeOver (κ := κ) G ι g H
  rw [he] at ht
  have hle : TangentBracket.matrixTangentSpanOver (κ := κ) G ι H ≤
      (TangentBracket.matrixTangentSpanOver (κ := κ) G ι H).comap
        ((TangentCone.matrixConjugation G ι g).toLinearMap.restrictScalars κ) := by
    apply Submodule.span_le.mpr
    exact fun X hX => Submodule.subset_span (ht hX)
  exact hle

end

section

attribute [local instance] LieRing.ofAssociativeRing

variable {F K κ : Type} [Field F] [NormedField K] [NontriviallyNormedField κ]
variable [CompleteSpace κ] [NormedAlgebra κ K] [FiniteDimensional κ K] {n : ℕ}

def matrixTangentLieSubalgebraOver (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n) (ι : F →+* K)
    (H : Subgroup (G.Points ι)) : LieSubalgebra κ (Matrix (Fin n) (Fin n) K) :=
  { TangentBracket.matrixTangentSpanOver (κ := κ) G ι H with
    lie_mem' := fun {_X _Y} hX hY =>
      tangentSpanOver_commutator_mem_of_conjugation_invariant G ι H _
        (TangentBracket.matrixTangentSpanOver (κ := κ) G ι H).closed_of_finiteDimensional
        (matrixTangentSpanOver_preserved_by_member G ι H) hY hX }

end

attribute [local instance] LieRing.ofAssociativeRing

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def finitePrimeTangentLie (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : HeightOneSpectrum (𝓞 F)) (H : Subgroup (LocalAdeles.LocalPoints G (Sum.inr v))) :
    LieSubalgebra (TangentBracket.closedPrimeSubfield (v.adicCompletion F))
      (Matrix (Fin n) (Fin n) (v.adicCompletion F)) := by
  let : NontriviallyNormedField (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) :=
    TangentBracket.finiteClosedPrimeNontriviallyNormedField v
  let : FiniteDimensional (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) (v.adicCompletion F) :=
    finiteCompletion_finiteDimensional_closedPrime v
  exact matrixTangentLieSubalgebraOver (κ := TangentBracket.closedPrimeSubfield (v.adicCompletion F))
    G (LocalAdeles.localEmbedding (Sum.inr v)) H

theorem finitePrimeTangentLie_nonzero (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup F n)
    (v : HeightOneSpectrum (𝓞 F)) (H : Subgroup (LocalAdeles.LocalPoints G (Sum.inr v)))
    (hd : ¬ IsDiscrete (H : Set (LocalAdeles.LocalPoints G (Sum.inr v)))) : finitePrimeTangentLie G v H ≠ ⊥ := by
  let : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  let : NontriviallyNormedField (TangentBracket.closedPrimeSubfield (v.adicCompletion F)) :=
    TangentBracket.finiteClosedPrimeNontriviallyNormedField v
  obtain ⟨X, hX, hne⟩ := TangentBracket.matrixTangentConeOver_nonzero
    (K := v.adicCompletion F) (κ := TangentBracket.closedPrimeSubfield (v.adicCompletion F))
    G (LocalAdeles.localEmbedding (Sum.inr v)) H hd
  intro he
  have hm : X ∈ finitePrimeTangentLie G v H := Submodule.subset_span hX
  rw [he, LieSubalgebra.mem_bot] at hm
  exact hne hm

end

section

/-! The norm of rational integers at a finite place, expressed through
the characteristic of the residue field. These estimates control local
analytic power series. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain

variable {F : Type} [Field F] [NumberField F]

def residuePrime (v : HeightOneSpectrum (𝓞 F)) : ℕ := ringChar ((𝓞 F) ⧸ v.asIdeal)

theorem residuePrime_prime (v : HeightOneSpectrum (𝓞 F)) : (residuePrime v).Prime :=
  CharP.char_is_prime ((𝓞 F) ⧸ v.asIdeal) (residuePrime v)

omit [NumberField F] in
theorem natCast_mem_prime_iff (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) :
    (m : 𝓞 F) ∈ v.asIdeal ↔ residuePrime v ∣ m := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  simp only [map_natCast, CharP.cast_eq_zero_iff ((𝓞 F) ⧸ v.asIdeal) (residuePrime v)]

theorem natCast_norm_lt_one_iff (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) :
    ‖(m : v.adicCompletion F)‖ < 1 ↔ residuePrime v ∣ m := by
  rw [Valued.toNormedField.norm_lt_one_iff,
    ← map_natCast (algebraMap F (v.adicCompletion F))]
  change Valued.v ((m : F) : v.adicCompletion F) < 1 ↔ _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    ← map_natCast (algebraMap (𝓞 F) F), HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_lt_one_iff_mem, natCast_mem_prime_iff]

theorem natCast_norm_le_one (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) :
    ‖(m : v.adicCompletion F)‖ ≤ 1 := by
  apply Valued.toNormedField.norm_le_one_iff.mpr
  rw [← map_natCast (algebraMap F (v.adicCompletion F))]
  change Valued.v ((m : F) : v.adicCompletion F) ≤ 1
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    ← map_natCast (algebraMap (𝓞 F) F), HeightOneSpectrum.valuation_of_algebraMap]
  exact v.intValuation_le_one _

theorem natCast_norm_eq_one_of_not_dvd (v : HeightOneSpectrum (𝓞 F)) (m : ℕ)
    (hm : ¬ residuePrime v ∣ m) : ‖(m : v.adicCompletion F)‖ = 1 :=
  le_antisymm (natCast_norm_le_one v m) (not_lt.mp ((natCast_norm_lt_one_iff v m).not.mpr hm))

theorem natCast_norm_eq_prime_pow (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) (hm : m ≠ 0) :
    ‖(m : v.adicCompletion F)‖ =
      ‖(residuePrime v : v.adicCompletion F)‖ ^ padicValNat (residuePrime v) m := by
  let : Fact (residuePrime v).Prime := ⟨residuePrime_prime v⟩
  obtain ⟨k, a, ha, hma⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm (residuePrime v)
    (residuePrime_prime v).ne_one
  have ha0 : a ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hma
    exact hm hma
  have hk : padicValNat (residuePrime v) m = k := by
    rw [hma, padicValNat.mul (pow_ne_zero _ (residuePrime_prime v).ne_zero) ha0,
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd ha, add_zero]
  rw [hk, hma, Nat.cast_mul, Nat.cast_pow, norm_mul, norm_pow,
    natCast_norm_eq_one_of_not_dvd v a ha, mul_one]

theorem residuePrime_norm_pos (v : HeightOneSpectrum (𝓞 F)) :
    0 < ‖(residuePrime v : v.adicCompletion F)‖ := by
  let : CharZero (v.adicCompletion F) := Algebra.charZero_of_charZero F (v.adicCompletion F)
  exact norm_pos_iff.mpr (Nat.cast_ne_zero.mpr (residuePrime_prime v).ne_zero)

theorem factorial_inverse_norm_le (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) :
    ‖((m.factorial : v.adicCompletion F)⁻¹)‖ ≤
      (‖(residuePrime v : v.adicCompletion F)‖⁻¹) ^ m := by
  let : Fact (residuePrime v).Prime := ⟨residuePrime_prime v⟩
  rw [norm_inv, natCast_norm_eq_prime_pow v _ (Nat.factorial_ne_zero m), ← inv_pow]
  apply pow_le_pow_right₀
  · exact (one_le_inv₀ (residuePrime_norm_pos v)).mpr (natCast_norm_le_one v _)
  · exact padicValNat_factorial_le (residuePrime v) m

end

/-! Positive convergence radius for the exponential series at finite
places, using the proved factorial norm bound. -/

open scoped Classical _root_.NumberField ENNReal NNReal
open IsDedekindDomain Filter _root_.Topology

variable {F : Type} [Field F] [NumberField F]

instance finiteCompletionNontriviallyNormedField (v : HeightOneSpectrum (𝓞 F)) :
    NontriviallyNormedField (v.adicCompletion F) :=
  Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))

theorem finite_expSeries_radius_pos (v : HeightOneSpectrum (𝓞 F))
    (A : Type*) [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] :
    0 < (NormedSpace.expSeries (v.adicCompletion F) A).radius := by
  let r : ℝ≥0 := ‖(residuePrime v : v.adicCompletion F)‖₊
  have hr : 0 < (r : ℝ) := residuePrime_norm_pos v
  have hbound : (r : ℝ≥0∞) ≤ (NormedSpace.expSeries (v.adicCompletion F) A).radius := by
    apply FormalMultilinearSeries.le_radius_of_eventually_le _ 1
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    have hcoeff : ‖NormedSpace.expSeries (v.adicCompletion F) A m‖ ≤
        ‖((m.factorial : v.adicCompletion F)⁻¹)‖ := by
      rw [NormedSpace.expSeries_eq_ofScalars]
      exact FormalMultilinearSeries.ofScalars_norm_le A _ m hm
    calc
      _ ≤ ‖((m.factorial : v.adicCompletion F)⁻¹)‖ * (r : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right hcoeff (pow_nonneg r.property _)
      _ ≤ ((r : ℝ)⁻¹) ^ m * (r : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right (factorial_inverse_norm_le v m) (pow_nonneg r.property _)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hr.ne', one_pow]
  exact (ENNReal.coe_pos.mpr (by exact_mod_cast hr)).trans_le hbound

theorem finite_exponential_hasPowerSeries (v : HeightOneSpectrum (𝓞 F))
    (A : Type*) [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A] :
    HasFPowerSeriesAt (NormedSpace.exp : A → A)
      (NormedSpace.expSeries (v.adicCompletion F) A) 0 := by
  let : CharZero (v.adicCompletion F) := Algebra.charZero_of_charZero F (v.adicCompletion F)
  exact NormedSpace.hasFPowerSeriesAt_exp_zero_of_radius_pos (finite_expSeries_radius_pos v A)

theorem finite_exponential_hasStrictFDerivAt (v : HeightOneSpectrum (𝓞 F))
    (A : Type*) [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A] :
    HasStrictFDerivAt (NormedSpace.exp : A → A) (ContinuousLinearMap.id (v.adicCompletion F) A) 0 := by
  have h := (finite_exponential_hasPowerSeries v A).hasStrictFDerivAt
  have he : continuousMultilinearCurryFin1 (v.adicCompletion F) A A
      (NormedSpace.expSeries (v.adicCompletion F) A 1) =
        ContinuousLinearMap.id (v.adicCompletion F) A := by
    ext X
    simp [NormedSpace.expSeries]
  rwa [he] at h

def finiteExponentialChart (v : HeightOneSpectrum (𝓞 F))
    (A : Type*) [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A] :
    OpenPartialHomeomorph A A :=
  (finite_exponential_hasStrictFDerivAt v A).toOpenPartialHomeomorph
    (f' := ContinuousLinearEquiv.refl (v.adicCompletion F) A) NormedSpace.exp

@[simp] theorem finiteExponentialChart_apply (v : HeightOneSpectrum (𝓞 F))
    (A : Type*) [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A] (X : A) :
    finiteExponentialChart v A X = NormedSpace.exp X := rfl

theorem zero_mem_finiteExponentialChart_source (v : HeightOneSpectrum (𝓞 F))
    (A : Type*) [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A] :
    (0 : A) ∈ (finiteExponentialChart v A).source :=
  (finite_exponential_hasStrictFDerivAt v A).mem_toOpenPartialHomeomorph_source
    (f' := ContinuousLinearEquiv.refl (v.adicCompletion F) A)

theorem one_mem_finiteExponentialChart_target (v : HeightOneSpectrum (𝓞 F))
    (A : Type*) [NormedRing A] [NormedAlgebra (v.adicCompletion F) A] [CompleteSpace A] :
    (1 : A) ∈ (finiteExponentialChart v A).target := by
  have h := (finiteExponentialChart v A).map_source (zero_mem_finiteExponentialChart_source v A)
  simpa only [finiteExponentialChart_apply, NormedSpace.exp_zero] using h

end

end OAI.NumberTheory.Quaternion.Arithmetic.LocalCompletion
