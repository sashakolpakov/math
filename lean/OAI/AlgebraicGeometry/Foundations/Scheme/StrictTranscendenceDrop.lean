import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Ideal.Quotient.Operations
import OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDegreeTransfer

/-! # Strict Transcendence Drop -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.StrictTranscendenceDrop

noncomputable section

/-!
# Strict transcendence-degree drop under a proper prime quotient

A surjective homomorphism between domains of finite transcendence degree cannot
preserve transcendence degree while having a nonzero kernel. The proof lifts a
transcendence basis and uses the fact that an algebraic domain extension cannot
acquire a kernel when the map on its base remains injective.
-/

open Function _root_.Algebra Cardinal

universe u v w

variable {k : Type v} [Field k]
variable {A B : Type u} [CommRing A] [IsDomain A] [CommRing B]
variable [Algebra k A] [Algebra k B]

/-- If an algebra homomorphism preserves algebraic independence of a
transcendence basis of its domain, the homomorphism is injective. -/
theorem injective_of_transcendenceBasis_image_independent
    {ι : Type w} {x : ι → A} (f : A →ₐ[k] B)
    (hx : IsTranscendenceBasis k x)
    (hfx : AlgebraicIndependent k (f ∘ x)) : Function.Injective f := by
  let S := Algebra.adjoin k (Set.range x)
  let : Algebra A B := f.toRingHom.toAlgebra
  let : Algebra.IsAlgebraic S A := hx.isAlgebraic
  have heval : MvPolynomial.aeval (f ∘ x) = f.comp (MvPolynomial.aeval x) := by
    ext i
    simp
  have hinj : Function.Injective (algebraMap S B) := by
    intro a b hab
    obtain ⟨p, rfl⟩ := hx.1.aevalEquiv.surjective a
    obtain ⟨q, rfl⟩ := hx.1.aevalEquiv.surjective b
    have hpq : p = q := by
      apply hfx
      rw [heval]
      change f (MvPolynomial.aeval x p) = f (MvPolynomial.aeval x q)
      exact hab
    exact congrArg hx.1.aevalEquiv hpq
  change Function.Injective (algebraMap A B)
  exact Algebra.IsAlgebraic.injective_tower_top (R := S) A hinj

variable [IsDomain B]

/-- With finite transcendence degree, a surjective noninjective homomorphism of
domains strictly decreases transcendence degree. -/
theorem trdeg_lt_of_surjective_not_injective
    (f : A →ₐ[k] B) (hf : Function.Surjective f) (hni : ¬ Function.Injective f)
    (hfin : Algebra.trdeg k A < ℵ₀) : Algebra.trdeg k B < Algebra.trdeg k A := by
  apply lt_of_not_ge
  intro hge
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k B
  choose x hx using (fun b : s => hf b.val)
  have hcomp : f ∘ x = (Subtype.val : s → B) := funext hx
  have hfx : AlgebraicIndependent k (f ∘ x) := by
    rw [hcomp]
    exact hs.1
  have hxind : AlgebraicIndependent k x := hfx.of_comp f
  have hxbasis : IsTranscendenceBasis k x :=
    hxind.isTranscendenceBasis_of_trdeg_le hfin
      (hge.trans_eq hs.cardinalMk_eq_trdeg.symm)
  exact hni (injective_of_transcendenceBasis_image_independent f hxbasis hfx)

/-- The finite-type version requires no separate transcendence-degree bound. -/
theorem trdeg_lt_of_surjective_not_injective_of_finiteType
    [Algebra.FiniteType k A] (f : A →ₐ[k] B)
    (hf : Function.Surjective f) (hni : ¬ Function.Injective f) :
    Algebra.trdeg k B < Algebra.trdeg k A :=
  trdeg_lt_of_surjective_not_injective f hf hni trdeg_lt_aleph0_of_finiteType

/-- A nonzero prime quotient of a finite-type domain has strictly smaller
transcendence degree over the coefficient field. -/
theorem trdeg_quotient_lt_of_prime_ne_bot [Algebra.FiniteType k A]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) :
    Algebra.trdeg k (A ⧸ p) < Algebra.trdeg k A := by
  apply trdeg_lt_of_surjective_not_injective_of_finiteType (Ideal.Quotient.mkₐ k p)
    Ideal.Quotient.mk_surjective
  intro hinj
  apply hp
  simpa using (RingHom.injective_iff_ker_eq_bot (Ideal.Quotient.mk p)).mp hinj

/-- The strict drop also holds for the transcendence degrees of the function
fields of the two domains. -/
theorem fractionRing_trdeg_quotient_lt_of_prime_ne_bot [Algebra.FiniteType k A]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) :
    Algebra.trdeg k (FractionRing (A ⧸ p)) < Algebra.trdeg k (FractionRing A) := by
  rw [← TranscendenceDegreeTransfer.trdeg_eq_fractionRing k (A ⧸ p), ← TranscendenceDegreeTransfer.trdeg_eq_fractionRing k A]
  exact trdeg_quotient_lt_of_prime_ne_bot p hp

/-- The natural-number version of strict transcendence-degree drop. Finiteness
comes from the finite-type hypothesis, so `Cardinal.toNat` loses no information. -/
theorem trdeg_toNat_quotient_lt_of_prime_ne_bot [Algebra.FiniteType k A]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) :
    (Algebra.trdeg k (A ⧸ p)).toNat < (Algebra.trdeg k A).toNat :=
  Cardinal.toNat_lt_toNat (trdeg_quotient_lt_of_prime_ne_bot p hp)
    trdeg_lt_aleph0_of_finiteType

/-- Strict inclusion of prime ideals reverses the transcendence degrees of
their quotient domains. The ambient finite-type ring need not be a domain. -/
theorem trdeg_quotient_lt_of_prime_lt
    {R : Type u} [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (hpq : p < q) :
    Algebra.trdeg k (R ⧸ q) < Algebra.trdeg k (R ⧸ p) := by
  apply trdeg_lt_of_surjective_not_injective_of_finiteType
    (Ideal.Quotient.factorₐ k hpq.le) (Ideal.Quotient.factor_surjective hpq.le)
  intro hinj
  apply not_le_of_gt hpq
  intro a ha
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hinj
  simpa only [Ideal.Quotient.factorₐ_apply_mk, map_zero] using
    (Ideal.Quotient.eq_zero_iff_mem.mpr ha : Ideal.Quotient.mk q a = 0)

/-- The natural-number dimension function obtained from transcendence degree
strictly decreases along strict inclusion of prime ideals. -/
theorem trdeg_toNat_quotient_lt_of_prime_lt
    {R : Type u} [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (hpq : p < q) :
    (Algebra.trdeg k (R ⧸ q)).toNat < (Algebra.trdeg k (R ⧸ p)).toNat :=
  Cardinal.toNat_lt_toNat (trdeg_quotient_lt_of_prime_lt hpq)
    trdeg_lt_aleph0_of_finiteType

end

end OAI.AlgebraicGeometry.Foundations.Scheme.StrictTranscendenceDrop
