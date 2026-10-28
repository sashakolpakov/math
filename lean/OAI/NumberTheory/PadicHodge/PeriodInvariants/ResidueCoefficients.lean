import OAI.NumberTheory.PadicHodge.PeriodInvariants.IntegralGeometry

/-! # Residue Coefficients -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ResidueCoefficients

noncomputable section

/-!
# Finite residue fields and the unramified coefficient field

Compactness of the valuation ring and openness of its maximal ideal prove that
the residue field of a finite p-adic extension is finite. Its Witt vectors and
fraction field are therefore the actual coefficient rings in crystalline cohomology.
-/

open scoped NNReal

universe u

open OAI.NumberTheory.PadicHodge.PeriodInvariants.IntegralGeometry

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) [Field K] [Algebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

instance residueField_finite : Finite (IntegralGeometry.ResidueField p K) := by
  let _ : NormedField K := spectralNorm.normedField ℚ_[p] K
  let _ : NormedAlgebra ℚ_[p] K := spectralNorm.normedAlgebra ℚ_[p] K
  let _ : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  have hset : (IntegralGeometry.ringOfIntegers p K : Set K) = Metric.closedBall (0 : K) 1 := by
    ext x
    change IntegralGeometry.fieldValuation p K x ≤ 1 ↔ dist x 0 ≤ 1
    rw [dist_zero_right]
    change ‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1
    exact NNReal.coe_le_coe.symm
  have hc : IsCompact (IntegralGeometry.ringOfIntegers p K : Set K) := hset ▸ isCompact_closedBall (0 : K) 1
  let _ : CompactSpace (IntegralGeometry.ringOfIntegers p K) := isCompact_iff_compactSpace.mp hc
  have hopen : IsOpen (IsLocalRing.maximalIdeal (IntegralGeometry.ringOfIntegers p K) : Set (IntegralGeometry.ringOfIntegers p K)) := by
    have he : (IsLocalRing.maximalIdeal (IntegralGeometry.ringOfIntegers p K) : Set (IntegralGeometry.ringOfIntegers p K)) =
        {a : IntegralGeometry.ringOfIntegers p K | ‖(a : K)‖ < 1} := by
      ext a
      have hm : a ∈ IsLocalRing.maximalIdeal (IntegralGeometry.ringOfIntegers p K) ↔
          IntegralGeometry.fieldValuation p K (a : K) < 1 :=
        Valuation.mem_maximalIdeal_iff K (IntegralGeometry.fieldValuation p K)
      have hn : IntegralGeometry.fieldValuation p K (a : K) < 1 ↔ ‖(a : K)‖ < 1 := by
        change ‖(a : K)‖₊ < 1 ↔ ‖(a : K)‖ < 1
        exact NNReal.coe_lt_coe.symm
      exact hm.trans hn
    rw [he]
    exact isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const
  let _ : TopologicalSpace (IntegralGeometry.ResidueField p K) :=
    inferInstanceAs (TopologicalSpace (IntegralGeometry.ringOfIntegers p K ⧸ IsLocalRing.maximalIdeal (IntegralGeometry.ringOfIntegers p K)))
  let _ : DiscreteTopology (IntegralGeometry.ResidueField p K) :=
    QuotientAddGroup.discreteTopology
      (N := (IsLocalRing.maximalIdeal (IntegralGeometry.ringOfIntegers p K)).toAddSubgroup) hopen
  let _ : CompactSpace (IntegralGeometry.ResidueField p K) :=
    inferInstanceAs (CompactSpace (IntegralGeometry.ringOfIntegers p K ⧸ IsLocalRing.maximalIdeal (IntegralGeometry.ringOfIntegers p K)))
  exact finite_of_compact_of_discrete

instance residueField_perfect : PerfectRing (IntegralGeometry.ResidueField p K) p := inferInstance

abbrev WittCoefficients := WittVector p (IntegralGeometry.ResidueField p K)

instance wittCoefficients_domain : IsDomain (WittCoefficients p K) := inferInstance

def padicIntToWitt : ℤ_[p] →+* WittCoefficients p K :=
  (WittVector.map (ZMod.castHom (dvd_refl p) (IntegralGeometry.ResidueField p K))).comp (WittVector.fromPadicInt p)

theorem padicIntToWitt_injective : Function.Injective (padicIntToWitt p K) :=
  (WittVector.map_injective (ZMod.castHom (dvd_refl p) (IntegralGeometry.ResidueField p K))
    (ZMod.castHom (dvd_refl p) (IntegralGeometry.ResidueField p K)).injective).comp (WittVector.equiv p).symm.injective

instance wittCoefficients_charZero : CharZero (WittCoefficients p K) :=
  (RingHom.charZero_iff (padicIntToWitt_injective p K)).mp inferInstance

/-- The actual maximal-unramified coefficient field W(k)[1/p], realized as the fraction field. -/
abbrev K0 := FractionRing (WittCoefficients p K)

instance k0_field : Field (K0 p K) := inferInstance

instance k0_charZero : CharZero (K0 p K) := inferInstance

/-- For the finite perfect residue field, the Witt fraction field is exactly W(k)[1/p]. -/
instance k0_localization : IsLocalization.Away (p : WittCoefficients p K) (K0 p K) := by
  apply IsLocalization.Away.mk (p : WittCoefficients p K)
  · apply isUnit_iff_ne_zero.mpr
    rw [map_natCast]
    exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  · intro z
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (WittCoefficients p K)) z
    obtain ⟨n, v, hv⟩ := WittVector.exists_eq_pow_p_mul' (b : WittCoefficients p K)
      (mem_nonZeroDivisors_iff_ne_zero.mp b.property)
    refine ⟨n, a * (↑v⁻¹ : WittCoefficients p K), ?_⟩
    apply mul_right_cancel₀ ((v.isUnit.map (algebraMap (WittCoefficients p K) (K0 p K))).ne_zero)
    calc
      (z * algebraMap (WittCoefficients p K) (K0 p K) (p : WittCoefficients p K) ^ n) *
          algebraMap (WittCoefficients p K) (K0 p K) v =
        z * algebraMap (WittCoefficients p K) (K0 p K) b := by
        rw [hv, map_mul, map_pow, mul_assoc]
      _ = algebraMap (WittCoefficients p K) (K0 p K) a := hab
      _ = _ := by rw [← map_mul, mul_assoc, Units.inv_mul, mul_one]
  · intro a b hab
    have he := IsFractionRing.injective (WittCoefficients p K) (K0 p K) hab
    exact ⟨0, by rw [he]⟩

def padicIntToK0 : ℤ_[p] →+* K0 p K :=
  (algebraMap (WittCoefficients p K) (K0 p K)).comp (padicIntToWitt p K)

theorem padicIntToK0_injective : Function.Injective (padicIntToK0 p K) :=
  (IsFractionRing.injective (WittCoefficients p K) (K0 p K)).comp (padicIntToWitt_injective p K)

def padicToK0 : ℚ_[p] →+* K0 p K :=
  IsLocalization.lift (S := ℚ_[p]) (g := padicIntToK0 p K) (fun x => by
    apply isUnit_iff_ne_zero.mpr
    intro h
    exact mem_nonZeroDivisors_iff_ne_zero.mp x.property
      (padicIntToK0_injective p K (h.trans (map_zero _).symm)))

instance k0_padicAlgebra : Algebra ℚ_[p] (K0 p K) := (padicToK0 p K).toAlgebra

theorem padicToK0_int (x : ℤ_[p]) :
    padicToK0 p K (algebraMap ℤ_[p] ℚ_[p] x) = padicIntToK0 p K x :=
  IsLocalization.lift_eq _ x

/-- Witt Frobenius on the unramified coefficient field. -/
def coefficientFrobenius : K0 p K ≃+* K0 p K :=
  IsFractionRing.ringEquivOfRingEquiv (WittVector.frobeniusEquiv p (IntegralGeometry.ResidueField p K))

theorem coefficientFrobenius_algebraMap (x : WittCoefficients p K) :
    coefficientFrobenius p K (algebraMap (WittCoefficients p K) (K0 p K) x) =
      algebraMap (WittCoefficients p K) (K0 p K) (WittVector.frobenius x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ x

theorem wittFrobenius_padicInt (x : ℤ_[p]) :
    WittVector.frobenius (padicIntToWitt p K x) = padicIntToWitt p K x := by
  change WittVector.frobenius
      (WittVector.map (ZMod.castHom (dvd_refl p) (IntegralGeometry.ResidueField p K)) (WittVector.fromPadicInt p x)) =
    WittVector.map (ZMod.castHom (dvd_refl p) (IntegralGeometry.ResidueField p K)) (WittVector.fromPadicInt p x)
  ext n
  simp only [WittVector.coeff_frobenius_charP, WittVector.map_coeff]
  rw [← map_pow, ZMod.pow_card]

theorem coefficientFrobenius_padicInt (x : ℤ_[p]) :
    coefficientFrobenius p K (padicIntToK0 p K x) = padicIntToK0 p K x := by
  change coefficientFrobenius p K
      (algebraMap (WittCoefficients p K) (K0 p K) (padicIntToWitt p K x)) = _
  rw [coefficientFrobenius_algebraMap, wittFrobenius_padicInt]
  rfl

theorem coefficientFrobenius_padic (x : ℚ_[p]) :
    coefficientFrobenius p K (padicToK0 p K x) = padicToK0 p K x := by
  have he : (coefficientFrobenius p K).toRingHom.comp (padicToK0 p K) = padicToK0 p K := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    ext a
    change coefficientFrobenius p K (padicToK0 p K (algebraMap ℤ_[p] ℚ_[p] a)) = _
    rw [padicToK0_int, coefficientFrobenius_padicInt]
    exact (padicToK0_int p K a).symm
  exact DFunLike.congr_fun he x

def coefficientFrobeniusAlg : K0 p K ≃ₐ[ℚ_[p]] K0 p K :=
  { coefficientFrobenius p K with commutes' := coefficientFrobenius_padic p K }

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ResidueCoefficients
