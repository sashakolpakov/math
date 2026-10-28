import OAI.AlgebraicGeometry.PELModuli.CMPoints.Arithmetic
import OAI.AlgebraicGeometry.ComplexMultiplication.CommonCMField

/-! # Splitting -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.Splitting

noncomputable section

/-! Complete splitting descends to subfields. Applying SplitPrimes to the normal
compositum therefore chooses one arbitrarily large prime for all fixed
number fields at once. No separate simultaneous-splitting input is used. -/

open scoped Classical
open _root_.NumberField

theorem principal_integer_comap
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    (f : K →+* L) (m : ℕ) (hm : m ≠ 0) :
    (Ideal.span ({(m : RingOfIntegers L)} : Set (RingOfIntegers L))).comap
      (RingOfIntegers.mapRingHom f) =
        Ideal.span ({(m : RingOfIntegers K)} : Set (RingOfIntegers K)) := by
  ext a
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
    have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have hmL : (m : L) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have he : f ((a : K) / (m : K)) = (b : L) := by
      have hb' := congrArg (fun z : RingOfIntegers L => (z : L)) hb
      change f (a : K) = (m : L) * (b : L) at hb'
      rw [map_div₀, map_natCast, hb', mul_div_cancel_left₀ _ hmL]
    have hint : IsIntegral ℤ ((a : K) / (m : K)) :=
      (isIntegral_algHom_iff f.toIntAlgHom f.injective).mp (he.symm ▸ b.property)
    let z : RingOfIntegers K := ⟨(a : K) / (m : K), hint⟩
    apply Ideal.mem_span_singleton.mpr
    refine ⟨z, ?_⟩
    apply Subtype.ext
    change (a : K) = (m : K) * ((a : K) / (m : K))
    exact (mul_div_cancel₀ _ hmK).symm
  · rintro ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ha
    apply Ideal.mem_span_singleton.mpr
    refine ⟨RingOfIntegers.mapRingHom f b, ?_⟩
    simpa only [map_mul, map_natCast] using congrArg (RingOfIntegers.mapRingHom f) hb

/-- A subring of a finite product of prime fields is another such product. -/
theorem subring_of_prime_field_product
    {R Idx : Type*} [CommRing R] [Finite Idx] [Nonempty Idx]
    (q : ℕ) [Fact q.Prime] (f : R →+* (Idx → ZMod q))
    (hf : Function.Injective f) :
    ∃ n : ℕ, Nonempty (R ≃+* (Fin n → ZMod q)) := by
  classical
  let : Finite R := Finite.of_injective f hf
  let : IsReduced R := isReduced_of_injective f hf
  let : CharP R q := f.charP hf q
  have hpow (x : R) : x ^ q = x := by
    apply hf
    ext i
    simpa only [map_pow, Pi.pow_apply] using ZMod.pow_card (f x i)
  have hfield : ∀ m : MaximalSpectrum R, Nonempty ((R ⧸ m.asIdeal) ≃+* ZMod q) := by
    intro m
    let : m.asIdeal.IsMaximal := m.isMaximal
    let : Field (R ⧸ m.asIdeal) := Ideal.Quotient.field _
    let φ : ZMod q →+* (R ⧸ m.asIdeal) :=
      (Ideal.Quotient.mk m.asIdeal).comp (ZMod.castHom (dvd_refl q) R)
    let : CharP (R ⧸ m.asIdeal) q :=
      CharP.of_ringHom_of_ne_zero φ q (Fact.out : q.Prime).ne_zero
    have hsurj : Function.Surjective φ := by
      intro y
      have hy : y ^ q = y := by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
        simpa only [map_pow] using congrArg (Ideal.Quotient.mk m.asIdeal) (hpow x)
      have hy' := (Subfield.mem_bot_iff_pow_eq_self (R ⧸ m.asIdeal) q).mpr hy
      obtain ⟨z, hz⟩ := (mem_bot_iff_intCast q (R ⧸ m.asIdeal)).mp hy'
      exact ⟨(z : ZMod q), by simpa only [map_intCast] using hz⟩
    exact ⟨(RingEquiv.ofBijective φ ⟨φ.injective, hsurj⟩).symm⟩
  let e := (IsArtinianRing.equivPi R).toRingEquiv.trans
    (RingEquiv.piCongrRight (fun m => (hfield m).some))
  let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  exact ⟨Fintype.card (MaximalSpectrum R),
    ⟨e.trans (RingEquiv.piCongrLeft' (fun _ : MaximalSpectrum R => ZMod q)
      (Fintype.equivFin (MaximalSpectrum R)))⟩⟩

theorem complete_splitting_descends
    {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    (f : K →+* L) (q : ℕ) [Fact q.Prime]
    (hsplit : Arithmetic.SplitsCompletelyAt L q) : Arithmetic.SplitsCompletelyAt K q := by
  let IK : Ideal (RingOfIntegers K) := Ideal.span {(q : RingOfIntegers K)}
  let IL : Ideal (RingOfIntegers L) := Ideal.span {(q : RingOfIntegers L)}
  let fO := RingOfIntegers.mapRingHom f
  have hc : IL.comap fO = IK := principal_integer_comap f q (Fact.out : q.Prime).ne_zero
  let φ : (RingOfIntegers K ⧸ IK) →+* (RingOfIntegers L ⧸ IL) :=
    Ideal.quotientMap IL fO hc.ge
  have hφ : Function.Injective φ := Ideal.quotientMap_injective' hc.le
  obtain ⟨eL⟩ := hsplit
  let ψ := eL.toRingHom.comp φ
  let : Nonempty (Fin (Module.finrank ℚ L)) :=
    Fin.pos_iff_nonempty.mp (Module.finrank_pos : 0 < Module.finrank ℚ L)
  obtain ⟨n, ⟨eK⟩⟩ := subring_of_prime_field_product q ψ (eL.injective.comp hφ)
  have hcard : Nat.card (RingOfIntegers K ⧸ IK) = q ^ Module.finrank ℚ K := by
    have h := Ideal.absNorm_span_natCast (S := RingOfIntegers K) q
    rw [RingOfIntegers.rank] at h
    exact h
  have hecard : Nat.card (RingOfIntegers K ⧸ IK) = q ^ n := by
    rw [Nat.card_congr eK.toEquiv]
    simp
  have hn : n = Module.finrank ℚ K :=
    Nat.pow_right_injective (Fact.out : q.Prime).two_le (hecard.symm.trans hcard)
  subst n
  exact ⟨eK⟩

/-- One SplitPrimes application handles all finitely many fixed fields and exclusions. -/
theorem exists_simultaneously_split_prime
    (hSplitPrimes : Arithmetic.SplitPrimesInput) {Idx : Type*} [Finite Idx]
    (L : Idx → Type*) [∀ i, Field (L i)] [∀ i, NumberField (L i)]
    (excluded : Finset ℕ) (bound : ℕ) :
    ∃ q : ℕ, q.Prime ∧ bound < q ∧ q ∉ excluded ∧
      ∀ i, Arithmetic.SplitsCompletelyAt (L i) q := by
  let C := ComplexMultiplication.CommonCMField.CM.conjugateCompositum L
  obtain ⟨q, hq, hb, hx, hs⟩ := Arithmetic.exists_split_prime_above hSplitPrimes C excluded bound
  let : Fact q.Prime := ⟨hq⟩
  refine ⟨q, hq, hb, hx, fun i => ?_⟩
  let σ : L i →ₐ[ℚ] ℂ := IsAlgClosed.lift
  exact complete_splitting_descends
    (ComplexMultiplication.CommonCMField.CM.conjugateCompositum.embedding L i σ).toRingHom q hs

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.Splitting
