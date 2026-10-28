import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline
import OAI.NumberTheory.PadicHodge.IntegralComparison.EnvelopeFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.EnvelopeResidue

/-! # Frobenius -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.Frobenius

noncomputable section

/-!
# IntegralComparison: actual Frobenius lifts on polynomial crystalline presentations

For a k-algebra C, use one polynomial variable for each element of C over
W(k). Sending each variable to its q-th power and fixing W(k) lifts the
actual q-power Frobenius of C. It descends modulo powers of p and induces
maps of the corresponding divided-power envelopes.
-/

universe u

open OAI.NumberTheory.PadicHodge.IntegralComparison.DividedPower.PowerEnvelope

variable (p : ℕ) [Fact p.Prime]
variable (k C : Type u) [Field k] [Fintype k] [CharP k p] [CommRing C] [Algebra k C]

local notation "W" => WittVector p k

abbrev Presentation := MvPolynomial C W

def coefficientReduction : W →+* C :=
  (algebraMap k C).comp WittVector.constantCoeff

def presentationReduction : Presentation p k C →+* C :=
  MvPolynomial.eval₂Hom (coefficientReduction p k C) id

omit [Fintype k] [CharP k p] in
lemma presentationReduction_surjective : Function.Surjective (presentationReduction p k C) :=
  fun c => ⟨MvPolynomial.X c, MvPolynomial.eval₂Hom_X' _ _ c⟩

/-- The explicit W(k)-linear q-Frobenius lift on the free presentation. -/
def polynomialFrobenius : Presentation p k C →ₐ[W] Presentation p k C :=
  MvPolynomial.aeval (fun c : C => MvPolynomial.X c ^ Fintype.card k)

omit [CharP k p] [CommRing C] [Algebra k C] in
lemma polynomialFrobenius_coefficients :
    (polynomialFrobenius p k C).toRingHom.comp MvPolynomial.C = MvPolynomial.C := by
  apply RingHom.ext
  intro w
  exact (polynomialFrobenius p k C).commutes w

omit [CharP k p] in
lemma polynomialFrobenius_reduction :
    (presentationReduction p k C).comp (polynomialFrobenius p k C).toRingHom =
      (FiniteField.frobeniusAlgHom k C).toRingHom.comp (presentationReduction p k C) := by
  apply MvPolynomial.ringHom_ext
  · intro w
    change presentationReduction p k C (polynomialFrobenius p k C (MvPolynomial.C w)) =
      FiniteField.frobeniusAlgHom k C (presentationReduction p k C (MvPolynomial.C w))
    have hw : polynomialFrobenius p k C (MvPolynomial.C w) = MvPolynomial.C w :=
      (polynomialFrobenius p k C).commutes w
    rw [hw]
    rw [show presentationReduction p k C (MvPolynomial.C w) = coefficientReduction p k C w from
      MvPolynomial.eval₂Hom_C _ _ w]
    exact ((FiniteField.frobeniusAlgHom k C).commutes (WittVector.constantCoeff w)).symm
  · intro c
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      polynomialFrobenius, MvPolynomial.aeval_X, map_pow, presentationReduction,
      MvPolynomial.eval₂Hom_X', id_eq]
    rfl

omit [Fintype k] [Fact p.Prime] in
include k in
lemma prime_zero : (p : C) = 0 := by
  have hk : (p : k) = 0 := (CharP.cast_eq_zero_iff k p p).mpr dvd_rfl
  simpa only [map_natCast, map_zero] using congrArg (algebraMap k C) hk

def levelIdeal (n : ℕ) : Ideal (Presentation p k C) :=
  Ideal.span {(p : Presentation p k C) ^ (n + 1)}

abbrev Level (n : ℕ) := Presentation p k C ⧸ levelIdeal p k C n

omit [Fintype k] in
lemma presentationReduction_kills_level (n : ℕ) :
    levelIdeal p k C n ≤ RingHom.ker (presentationReduction p k C) := by
  rw [levelIdeal, Ideal.span_le]
  rintro x (rfl : x = _)
  change presentationReduction p k C ((p : Presentation p k C) ^ (n + 1)) = 0
  rw [map_pow, map_natCast, prime_zero p k C, zero_pow (Nat.succ_ne_zero _)]

def levelReduction (n : ℕ) : Level p k C n →+* C :=
  Ideal.Quotient.lift _ (presentationReduction p k C)
    (presentationReduction_kills_level p k C n)

omit [CharP k p] [CommRing C] [Algebra k C] in
lemma polynomialFrobenius_preserves_level (n : ℕ) :
    levelIdeal p k C n ≤ (levelIdeal p k C n).comap (polynomialFrobenius p k C).toRingHom := by
  rw [levelIdeal, Ideal.span_le]
  rintro x (rfl : x = _)
  change polynomialFrobenius p k C ((p : Presentation p k C) ^ (n + 1)) ∈ levelIdeal p k C n
  rw [map_pow, map_natCast]
  exact Ideal.subset_span (Set.mem_singleton _)

def levelFrobenius (n : ℕ) : Level p k C n →+* Level p k C n :=
  Ideal.quotientMap _ (polynomialFrobenius p k C).toRingHom
    (polynomialFrobenius_preserves_level p k C n)

lemma levelFrobenius_reduction (n : ℕ) :
    (levelReduction p k C n).comp (levelFrobenius p k C n) =
      (FiniteField.frobeniusAlgHom k C).toRingHom.comp (levelReduction p k C n) := by
  apply RingHom.ext
  intro x
  obtain ⟨e, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun (polynomialFrobenius_reduction p k C) e

def levelCoefficientMap (n : ℕ) : W →+* Level p k C n :=
  (Ideal.Quotient.mk _).comp MvPolynomial.C

omit [Fintype k] in
lemma levelReduction_surjective (n : ℕ) : Function.Surjective (levelReduction p k C n) := by
  intro c
  exact ⟨Ideal.Quotient.mk _ (MvPolynomial.X c), MvPolynomial.eval₂Hom_X' _ _ c⟩

omit [Fintype k] in
lemma levelReduction_coefficients (n : ℕ) :
    (levelReduction p k C n).comp (levelCoefficientMap p k C n) = coefficientReduction p k C := by
  apply RingHom.ext
  intro w
  exact MvPolynomial.eval₂Hom_C _ _ w

omit [CharP k p] [CommRing C] [Algebra k C] in
lemma levelFrobenius_coefficients (n : ℕ) :
    (levelFrobenius p k C n).comp (levelCoefficientMap p k C n) = levelCoefficientMap p k C n := by
  apply RingHom.ext
  intro w
  change Ideal.Quotient.mk _ (polynomialFrobenius p k C (MvPolynomial.C w)) =
    Ideal.Quotient.mk _ (MvPolynomial.C w)
  exact congrArg (Ideal.Quotient.mk _) (DFunLike.congr_fun (polynomialFrobenius_coefficients p k C) w)

def levelKernel (n : ℕ) : Ideal (Level p k C n) := RingHom.ker (levelReduction p k C n)

omit [Fintype k] in
lemma baseIdeal_le_levelKernel (n : ℕ) :
    Ideal.span {(p : W)} ≤ (levelKernel p k C n).comap (levelCoefficientMap p k C n) := by
  rw [Ideal.span_le]
  rintro x (rfl : x = _)
  change levelReduction p k C n (levelCoefficientMap p k C n (p : W)) = 0
  rw [map_natCast, map_natCast, prime_zero p k C]

lemma levelFrobenius_preserves_kernel (n : ℕ) :
    levelKernel p k C n ≤ (levelKernel p k C n).comap (levelFrobenius p k C n) := by
  intro x hx
  change levelReduction p k C n (levelFrobenius p k C n x) = 0
  have hc := DFunLike.congr_fun (levelFrobenius_reduction p k C n) x
  change levelReduction p k C n (levelFrobenius p k C n x) =
    FiniteField.frobeniusAlgHom k C (levelReduction p k C n x) at hc
  rw [hc, hx, map_zero]

omit [Fintype k] [CharP k p] [CommRing C] [Algebra k C] in
lemma level_prime_nilpotent (n : ℕ) : IsNilpotent (p : Level p k C n) := by
  refine ⟨n + 1, ?_⟩
  rw [← map_natCast (Ideal.Quotient.mk (levelIdeal p k C n)) p, ← map_pow,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

local notation "γ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k

/-- An actual finite-level divided-power envelope of the free presentation. -/
abbrev CrystallinePresentation (n : ℕ) :=
  DividedPower.PowerEnvelope.Envelope W (Level p k C n) (Ideal.span {(p : W)}) γ
    (levelCoefficientMap p k C n) (levelKernel p k C n)

abbrev crystallineIdeal (n : ℕ) :=
  DividedPower.PowerEnvelope.envelopeIdeal W (Level p k C n) (Ideal.span {(p : W)}) γ
    (levelCoefficientMap p k C n) (levelKernel p k C n)

abbrev crystallineDividedPowers (n : ℕ) :=
  DividedPower.PowerEnvelope.envelopeDividedPowers W (Level p k C n) (Ideal.span {(p : W)}) γ
    (levelCoefficientMap p k C n) (levelKernel p k C n)

/-- The explicit q-Frobenius lift, extended to the divided-power envelope. -/
def presentationFrobenius (n : ℕ) :
    DividedPowers.DPMorphism (crystallineDividedPowers p k C n) (crystallineDividedPowers p k C n) :=
  EnvelopeFunctor.endomorphism W (Level p k C n) (Ideal.span {(p : W)}) γ
    (levelCoefficientMap p k C n) (levelKernel p k C n) (baseIdeal_le_levelKernel p k C n)
    (DividedPowers.DPMorphism.id γ) (levelFrobenius p k C n)
    (levelFrobenius_coefficients p k C n) (levelFrobenius_preserves_kernel p k C n)

omit [Fintype k] in
lemma crystalline_prime_nilpotent (n : ℕ) : IsNilpotent (p : CrystallinePresentation p k C n) :=
  EnvelopeResidue.prime_nilpotent W (Level p k C n) (Ideal.span {(p : W)}) γ
    (levelCoefficientMap p k C n) (levelKernel p k C n) p (level_prime_nilpotent p k C n)

omit [Fintype k] in
lemma crystalline_nilIdeal (n : ℕ) {x : CrystallinePresentation p k C n}
    (hx : x ∈ crystallineIdeal p k C n) : IsNilpotent x :=
  DividedPower.Nilpotence.nilpotent_of_mem
    (A := CrystallinePresentation p k C n) (I := crystallineIdeal p k C n)
    (crystallineDividedPowers p k C n) p (Fact.out : p.Prime).pos
    (crystalline_prime_nilpotent p k C n) hx

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.Frobenius
