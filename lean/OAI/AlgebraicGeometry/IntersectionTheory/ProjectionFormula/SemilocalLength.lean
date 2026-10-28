import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilocalPID
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Normalization.Length
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-! # Semilocal Length -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilocalLength

noncomputable section

/-!
# ProjectionFormula: residue-weighted lengths over a possibly singular local base

A finite Dedekind algebra over a local ring can have several branches.
The length of its quotient by a nonzero ideal is the sum of the residue
degrees of its prime factors, with repetition. The base need not be normal.
-/

open IsLocalRing UniqueFactorizationMonoid
open scoped Classical

variable {R S : Type*} [CommRing R] [CommRing S]
  [IsLocalRing R] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S]

theorem length_quotient_prime (P : Ideal S) (hP : Prime P) :
    Module.length R (S ⧸ P) = (P.inertiaDeg R : ℕ∞) := by
  let : P.IsMaximal := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
  have hunder : P.under R = maximalIdeal R := eq_maximalIdeal inferInstance
  let : P.LiesOver (maximalIdeal R) :=
    hunder ▸ inferInstanceAs (P.LiesOver (P.under R))
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  let : Module.Finite (R ⧸ maximalIdeal R) (S ⧸ P) :=
    Module.Finite.of_restrictScalars_finite R (R ⧸ maximalIdeal R) (S ⧸ P)
  rw [Ideal.inertiaDeg_eq_of_isMaximal (maximalIdeal R) P,
    Module.length_eq_of_surjective (R := R ⧸ maximalIdeal R) (S := R)
      (M := S ⧸ P) Ideal.Quotient.mk_surjective,
    Module.length_eq_finrank]

theorem length_quotient_ideal_mul (I J : Ideal S) (hJ : J ≠ ⊥) :
    Module.length R (S ⧸ I * J) =
      Module.length R (S ⧸ I) + Module.length R (S ⧸ J) := by
  let : IsPrincipalIdealRing S := SemilocalPID.isPrincipalIdealRing R S
  have hJn : Submodule.IsPrincipal.generator J ≠ 0 :=
    fun h => hJ ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero J).mpr h)
  have h := Normalization.Length.length_quotient_mul (R := R)
    (Submodule.IsPrincipal.generator I) (Submodule.IsPrincipal.generator J) hJn
  rw [← Ideal.span_singleton_mul_span_singleton,
    Ideal.span_singleton_generator, Ideal.span_singleton_generator] at h
  exact h

/-- Each prime factor contributes the degree of its actual residue field.
Repeated factors count the order of vanishing at that branch. -/
theorem length_quotient_eq_sum (I : Ideal S) (hI : I ≠ ⊥) :
    Module.length R (S ⧸ I) =
      (((normalizedFactors I).map (fun P => P.inertiaDeg R)).sum : ℕ) := by
  have hprod : ∀ l : Multiset (Ideal S), (∀ P ∈ l, Prime P) →
      Module.length R (S ⧸ l.prod) =
        ((l.map (fun P => P.inertiaDeg R)).sum : ℕ) := by
    intro l
    induction l using Multiset.induction_on with
    | empty =>
      intro _
      simp only [Multiset.prod_zero, Multiset.map_zero, Multiset.sum_zero,
        Nat.cast_zero]
      have htop : (1 : Ideal S) = ⊤ := Ideal.one_eq_top
      exact (show Module.length R (S ⧸ (1 : Ideal S)) = 0 from by
        rw [htop]
        exact Module.length_eq_zero)
    | @cons P l ih =>
      intro h
      have hlnz : l.prod ≠ (0 : Ideal S) :=
        Multiset.prod_ne_zero (fun h0 => (h 0 (Multiset.mem_cons_of_mem h0)).ne_zero rfl)
      rw [Multiset.prod_cons, length_quotient_ideal_mul P l.prod hlnz,
        length_quotient_prime P (h P (Multiset.mem_cons_self P l)),
        ih (fun Q hQ => h Q (Multiset.mem_cons_of_mem hQ)),
        Multiset.map_cons, Multiset.sum_cons, Nat.cast_add]
  have hfactor : (normalizedFactors I).prod = I := by
    simpa only [normalize_eq] using prod_normalizedFactors_eq hI
  have h := hprod (normalizedFactors I) prime_of_normalized_factor
  rw [hfactor] at h
  exact h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SemilocalLength
