import OAI.NumberTheory.Splitting.Schur
import OAI.NumberTheory.Splitting.Polynomial
import OAI.NumberTheory.Splitting.Integral
import Lean.Util.CollectAxioms

/-! # Split Primes -/

namespace OAI.NumberTheory.Splitting.SplitPrimes.Construction

/-!
SplitPrimes: infinitely many completely split primes in a finite Galois extension
of ℚ. The splitting predicate below is the unchanged residue-ring definition
from Statements/SplitPrimes.lean, in a separate namespace. The proof uses Schur's
elementary prime-divisor argument and Galois normality, not density estimates.
-/

open _root_.Polynomial _root_.NumberField
open scoped _root_.NumberField

def SplitsCompletelyAt
    (L : Type*) [Field L] [NumberField L] (p : ℕ) : Prop :=
  Nonempty
    ((NumberField.RingOfIntegers L ⧸
        Ideal.span ({(p : NumberField.RingOfIntegers L)} :
          Set (NumberField.RingOfIntegers L))) ≃+*
      (Fin (Module.finrank ℚ L) → ZMod p))

/-- A simple root of the primitive polynomial gives a rational residue map;
normality then makes all roots rational, and Chinese remainders give the
complete splitting isomorphism. -/
theorem splitsCompletelyAt_of_root
    (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (B : PowerBasis ℚ L) (hint : IsIntegral ℤ B.gen)
    (p : ℕ) [Fact p.Prime]
    (he : ¬ p ∣ RingOfIntegers.exponent (⟨B.gen, hint⟩ : 𝓞 L))
    (hs : ((minpoly ℤ (⟨B.gen, hint⟩ : 𝓞 L)).map
      (Int.castRingHom (ZMod p))).Separable)
    (n : ℤ) (hn : (p : ℤ) ∣ (minpoly ℤ (⟨B.gen, hint⟩ : 𝓞 L)).eval n) :
    SplitsCompletelyAt L p := by
  let θ : 𝓞 L := ⟨B.gen, hint⟩
  let f := minpoly ℤ θ
  let g := f.map (Int.castRingHom (ZMod p))
  have hm : f.Monic := minpoly.monic θ.isIntegral
  have hroot : g.eval₂ (RingHom.id _) (n : ZMod p) = 0 := by
    have hzero : ((f.eval n : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hn
    simpa [g, eval₂_id, eval_map, eval₂_at_intCast] using hzero
  let e := RingOfIntegers.ZModXQuotSpanEquivQuotSpan he
  let φ : 𝓞 L →+* ZMod p :=
    (AdjoinRoot.lift (RingHom.id (ZMod p)) (n : ZMod p) hroot).comp
      (e.symm.toRingHom.comp (Ideal.Quotient.mk _))
  have hcomp : φ.comp (algebraMap ℤ (𝓞 L)) = Int.castRingHom (ZMod p) := by
    ext
    simp
  have hsplit : g.Splits := by
    simpa only [Polynomial.map_map, hcomp] using (Integral.SplitPrimesConstruction.integral_minpoly_splits L θ).map φ
  obtain ⟨q⟩ := Splitting.Polynomial.SplitPrimesConstruction.quotient_equiv_fun_of_splits_separable g (hm.map _) hsplit hs
  have hd : g.natDegree = Module.finrank ℚ L := by
    rw [show g.natDegree = f.natDegree from hm.natDegree_map _]
    have h := congrArg Polynomial.natDegree
      (minpoly.isIntegrallyClosed_eq_field_fractions ℚ L θ.isIntegral)
    rw [hm.natDegree_map] at h
    change (minpoly ℚ B.gen).natDegree = f.natDegree at h
    rw [← h, B.natDegree_minpoly, B.finrank]
  exact ⟨e.symm.trans (q.trans
    (RingEquiv.piCongrLeft' (fun _ : Fin g.natDegree ↦ ZMod p) (finCongr hd)))⟩

/-- SplitPrimes, with any fixed finite set of rational primes excluded. -/
theorem chebotarev_splitting
    (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (excluded : Finset ℕ) :
    Set.Infinite
      {p : ℕ | p.Prime ∧ p ∉ excluded ∧ SplitsCompletelyAt L p} := by
  classical
  obtain ⟨B, hint⟩ := Integral.SplitPrimesConstruction.exists_integral_powerBasis L
  let θ : 𝓞 L := ⟨B.gen, hint⟩
  let f := minpoly ℤ θ
  have hf : f.natDegree ≠ 0 := (minpoly.natDegree_pos θ.isIntegral).ne'
  have hfsep : (f.map (Int.castRingHom ℚ)).Separable := by
    have h := Algebra.IsSeparable.isSeparable ℚ (B.gen)
    change (minpoly ℚ (algebraMap (𝓞 L) L θ)).Separable at h
    rw [minpoly.isIntegrallyClosed_eq_field_fractions ℚ L θ.isIntegral] at h
    exact h
  obtain ⟨d, hd, hsep⟩ := Splitting.Polynomial.SplitPrimesConstruction.exists_separability_denominator f hf hfsep
  have he : RingOfIntegers.exponent θ ≠ 0 := Integral.SplitPrimesConstruction.integral_generator_exponent_ne_zero L B hint
  apply Set.infinite_iff_exists_gt.mpr
  intro bound
  let M := max bound (excluded.sup id)
  let m : ℤ := d * (RingOfIntegers.exponent θ : ℤ) * (M.factorial : ℤ)
  have hm : m ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hd (by exact_mod_cast he)) (by exact_mod_cast M.factorial_ne_zero)
  obtain ⟨p, hp, hpm, n, _, hpn⟩ := Schur.SplitPrimesConstruction.exists_prime_dvd_eval_avoiding f hf m hm
  have hpM : M < p := by
    by_contra! h
    have hpFac : p ∣ M.factorial := hp.dvd_factorial.mpr h
    apply hpm
    exact dvd_mul_of_dvd_right (by exact_mod_cast hpFac) _
  have hpd : ¬ (p : ℤ) ∣ d := fun h ↦
    hpm (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _)
  have hpe : ¬ p ∣ RingOfIntegers.exponent θ := by
    intro h
    apply hpm
    apply dvd_mul_of_dvd_left
    exact dvd_mul_of_dvd_right (by exact_mod_cast h) _
  refine ⟨p, ⟨hp, ?_, ?_⟩, (le_max_left _ _).trans_lt hpM⟩
  · intro h
    have hle : p ≤ excluded.sup id := Finset.le_sup (f := id) h
    exact (not_le_of_gt hpM) (hle.trans (le_max_right _ _))
  · have : Fact p.Prime := ⟨hp⟩
    exact splitsCompletelyAt_of_root L B hint p hpe (hsep p hp hpd) n hpn

end OAI.NumberTheory.Splitting.SplitPrimes.Construction
