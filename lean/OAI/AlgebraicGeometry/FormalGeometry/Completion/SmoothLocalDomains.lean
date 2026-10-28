import OAI.AlgebraicGeometry.FormalGeometry.Completion.EtaleDomainLocalization
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-! # Smooth Local Domains -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothLocalDomains.Construction

noncomputable section

/-!
# Completion: local rings of smooth algebras over fields are domains

The standard smooth local presentation is étale over a polynomial ring.
The proved integral-closure argument applies there and transfers back to
the actual localization at the original prime.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v

variable (K : Type u) (S : Type v) [Field K] [CommRing S] [Algebra K S]
  [Algebra.Smooth K S]

include K

/-- Every prime localization of an actual smooth field algebra is a normal domain. -/
theorem smooth_field_localization_isNormalDomain (p : Ideal S) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) := by
  obtain ⟨r, hr, n, a, hTower, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (p := p)
  let := a
  have := hTower
  have := hEtale
  let P := MvPolynomial (Fin n) K
  let S' := Localization.Away r
  let q : Ideal S' := p.map (algebraMap S S')
  have hd : Disjoint (Submonoid.powers r : Set S) p :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hr
  have : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers r) S' p inferInstance hd
  have hq : q.comap (algebraMap S S') = p :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers r) S' inferInstance hd
  have : IsDomain (Localization.AtPrime q) :=
    EtaleDomainLocalization.Construction.etale_localization_isDomain P (FractionRing P) S' q
  have : IsIntegrallyClosed (Localization.AtPrime q) :=
    EtaleDomainLocalization.Construction.etale_localization_isIntegrallyClosed P (FractionRing P) S' q
  have : IsLocalization.AtPrime (Localization.AtPrime q) p := by
    simpa only [hq] using IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (.powers r) (Localization.AtPrime q) q
  let e := (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
    (Localization.AtPrime q)).toRingEquiv
  exact ⟨e.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e.symm⟩

/-- Every prime localization of an actual smooth algebra over a field is a domain. -/
theorem smooth_field_localization_isDomain (p : Ideal S) [p.IsPrime] :
    IsDomain (Localization.AtPrime p) := (smooth_field_localization_isNormalDomain K S p).1

/-- Every prime localization of an actual smooth field algebra is integrally closed. -/
theorem smooth_field_localization_isIntegrallyClosed (p : Ideal S) [p.IsPrime] :
    IsIntegrallyClosed (Localization.AtPrime p) :=
  (smooth_field_localization_isNormalDomain K S p).2

/-- A smooth field algebra which is a domain is integrally closed. -/
theorem smooth_field_domain_isIntegrallyClosed [IsDomain S] : IsIntegrallyClosed S :=
  IsIntegrallyClosed.of_localization_maximal
    (fun p _ _ => smooth_field_localization_isIntegrallyClosed K S p)

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.SmoothLocalDomains.Construction
