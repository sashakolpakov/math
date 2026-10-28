import Mathlib

/-! # Arithmetic -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.Arithmetic

noncomputable section

section

/-!
Arithmetic choices for CMPoints. The completion is an actual adic completion,
and the comparison with Q_q commutes with the embeddings in algebraic
closures. Integral embeddings are specified by a commuting square, not by
an ordinary-reduction condition. Existence remains a theorem conclusion.
-/

open scoped Classical

open _root_.NumberField IsDedekindDomain

def SplitsCompletelyAt (K : Type*) [Field K] [NumberField K] (q : ℕ) : Prop :=
  Nonempty ((RingOfIntegers K ⧸
    Ideal.span ({(q : RingOfIntegers K)} : Set (RingOfIntegers K))) ≃+*
      (Fin (Module.finrank ℚ K) → ZMod q))

/-- CM conjugation, explicitly restricted to rational scalars. -/
def rationalConjugation (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] : Gal(E/ℚ) :=
  (NumberField.IsCMField.complexConj E).restrictScalars ℚ

/-- A chosen embedding into Qqbar, with the chosen completion literally
identified with Q_q. None of the fields asserts ordinary reduction. -/
structure QadicChoice (K : Type) [Field K] [NumberField K]
    (κ : K →+* ℂ) (q : ℕ) [Fact q.Prime] where
  complexClosure : AlgebraicClosure ℚ →+* ℂ
  fieldInClosure : K →+* AlgebraicClosure ℚ
  complex_compatibility : complexClosure.comp fieldInClosure = κ
  iota : AlgebraicClosure ℚ →+* AlgebraicClosure (Padic q)
  prime : HeightOneSpectrum (RingOfIntegers K)
  liesOver : (q : RingOfIntegers K) ∈ prime.asIdeal
  completion : prime.adicCompletion K ≃+* Padic q
  completion_continuous : Continuous completion
  completion_inverse_continuous : Continuous completion.symm
  closure_compatibility :
    iota.comp fieldInClosure =
      (algebraMap (Padic q) (AlgebraicClosure (Padic q))).comp
        (completion.toRingHom.comp (NumberField.FinitePlace.embedding prime))
  integralEmbedding : RingOfIntegers K →+* PadicInt q
  integral_compatibility :
    PadicInt.Coe.ringHom.comp integralEmbedding =
      (completion.toRingHom.comp (NumberField.FinitePlace.embedding prime)).comp
        (algebraMap (RingOfIntegers K) K)

namespace QadicChoice

variable {K : Type} [Field K] [NumberField K] {κ : K →+* ℂ}
  {q : ℕ} [Fact q.Prime] (j : QadicChoice K κ q)

def residue : RingOfIntegers K →+* ZMod q :=
  PadicInt.toZMod.comp j.integralEmbedding

def localCharacter {E : Type} [Field E] [NumberField E] [Algebra ℚ E] (iota : E →+* K)
    (τ : E ≃ₐ[ℚ] E) : RingOfIntegers E →+* PadicInt q :=
  j.integralEmbedding.comp
    (NumberField.RingOfIntegers.mapRingHom (iota.comp τ.toRingHom))

def residueCharacter {E : Type} [Field E] [NumberField E] [Algebra ℚ E] (iota : E →+* K)
    (τ : E ≃ₐ[ℚ] E) (n : ℕ) : RingOfIntegers E →+* ZMod (q ^ n) :=
  (PadicInt.toZModPow n).comp (j.localCharacter iota τ)

theorem residueCharacter_compatible {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    (iota : E →+* K) (τ : E ≃ₐ[ℚ] E) (m n : ℕ) (h : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow q h) (ZMod (q ^ m))).comp
      (j.residueCharacter iota τ n) = j.residueCharacter iota τ m := by
  rw [QadicChoice.residueCharacter, ← RingHom.comp_assoc, PadicInt.zmod_cast_comp_toZModPow m n h]
  rfl

/-- The actual prime of E determined by iota composed with τ. -/
def place {E : Type} [Field E] [NumberField E] [Algebra ℚ E] (iota : E →+* K)
    (τ : Gal(E/ℚ)) : HeightOneSpectrum (RingOfIntegers E) where
  asIdeal := RingHom.ker (PadicInt.toZMod.comp (j.localCharacter iota τ))
  isPrime := RingHom.ker_isPrime _
  ne_bot := by
    intro h
    have hq : (q : RingOfIntegers E) ∈
        RingHom.ker (PadicInt.toZMod.comp (j.localCharacter iota τ)) := by
      change (PadicInt.toZMod.comp (j.localCharacter iota τ)) q = 0
      simp
    rw [h, Ideal.mem_bot] at hq
    exact (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero) hq

def residueCoordinates {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    (iota : E →+* K) (n : ℕ) : RingOfIntegers E →+* (Gal(E/ℚ) → ZMod (q ^ n)) where
  toFun a τ := j.residueCharacter iota τ n a
  map_one' := by ext τ; exact map_one _
  map_mul' a b := by ext τ; exact map_mul _ a b
  map_zero' := by ext τ; exact map_zero _
  map_add' a b := by ext τ; exact map_add _ a b

/-- Literal splitting modulo every q-power, with the embedding labels fixed.
This is an arithmetic conclusion, never a hypothesis about ordinary fibers. -/
def HasSplitCoordinates {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    (iota : E →+* K) : Prop :=
  ∀ n : ℕ, Function.Surjective (j.residueCoordinates iota n) ∧
    RingHom.ker (j.residueCoordinates iota n) =
      Ideal.span ({(q ^ n : RingOfIntegers E)} : Set (RingOfIntegers E))

def projector {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
    (n : ℕ) (τ : Gal(E/ℚ)) : RingOfIntegers E :=
  ((hsplit n).1 (Pi.single τ 1)).choose

theorem projector_coordinates {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    (iota : E →+* K) (hsplit : j.HasSplitCoordinates iota)
    (n : ℕ) (τ : Gal(E/ℚ)) :
    j.residueCoordinates iota n (j.projector iota hsplit n τ) = Pi.single τ 1 :=
  ((hsplit n).1 (Pi.single τ 1)).choose_spec

end QadicChoice

/-- The exact SplitPrimes input, as a named proposition rather than a theorem stub. -/
def SplitPrimesInput : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    (excluded : Finset ℕ),
    Set.Infinite {q : ℕ | q.Prime ∧ q ∉ excluded ∧ SplitsCompletelyAt L q}

theorem exists_split_prime_above (hSplitPrimes : SplitPrimesInput)
    (L : Type) [Field L] [NumberField L] [IsGalois ℚ L]
    (excluded : Finset ℕ) (bound : ℕ) :
    ∃ q : ℕ, q.Prime ∧ bound < q ∧ q ∉ excluded ∧ SplitsCompletelyAt L q := by
  obtain ⟨q, hq, hbound⟩ := Set.infinite_iff_exists_gt.mp (hSplitPrimes L excluded) bound
  exact ⟨q, hq.1, hbound, hq.2⟩

end

/-! The exact kernel is forced by surjectivity and the actual cardinality
of the ring of integers modulo an integer. -/

open _root_.NumberField

theorem coordinate_kernel_of_surjective
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [IsGalois ℚ E]
    (m : ℕ) (hm : m ≠ 0)
    (φ : RingOfIntegers E →+* (Gal(E/ℚ) → ZMod m))
    (hφ : Function.Surjective φ) :
    RingHom.ker φ = Ideal.span ({(m : RingOfIntegers E)} : Set (RingOfIntegers E)) := by
  let : NeZero m := ⟨hm⟩
  let I : Ideal (RingOfIntegers E) := Ideal.span {(m : RingOfIntegers E)}
  have hI : I ≤ RingHom.ker φ := by
    apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    change φ (m : RingOfIntegers E) = 0
    ext τ
    simp
  let H (a : RingOfIntegers E) (ha : a ∈ I) : φ a = 0 := hI ha
  let F := Ideal.Quotient.lift I φ H
  have hcard : Nat.card (RingOfIntegers E ⧸ I) = m ^ Module.finrank ℚ E := by
    have h := Ideal.absNorm_span_natCast (S := RingOfIntegers E) m
    rw [RingOfIntegers.rank] at h
    have hA : (inferInstance : Algebra ℚ E) =
        (DivisionRing.toRatAlgebra : Algebra ℚ E) := Subsingleton.elim _ _
    have hdim := congrArg (fun A : Algebra ℚ E =>
      @Module.finrank ℚ E _ _ (@Algebra.toModule ℚ E _ _ A)) hA
    rw [hdim]
    exact h
  let : Finite (RingOfIntegers E ⧸ I) :=
    Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero _ hm)
  have htarget : Nat.card (Gal(E/ℚ) → ZMod m) = m ^ Module.finrank ℚ E := by
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := ZMod m), ZMod.card,
      IsGalois.card_aut_eq_finrank]
  have hsurj : Function.Surjective F := Ideal.Quotient.lift_surjective_of_surjective I H hφ
  have hinj : Function.Injective F :=
    ((Nat.bijective_iff_surjective_and_card F).mpr
      ⟨hsurj, hcard.trans htarget.symm⟩).1
  exact (Ideal.injective_lift_iff H).mp hinj

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.Arithmetic
