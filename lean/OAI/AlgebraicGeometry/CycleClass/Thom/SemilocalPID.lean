import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! # Semilocal PID -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.SemilocalPID.Constructions

/-! A finite Dedekind algebra over a local ring is semilocal, hence a PID.
This applies to finite normalizations of one-dimensional local domains. -/

theorem finite_maximalIdeals (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing R] [Algebra R S] [Module.Finite R S] :
    {P : Ideal S | P.IsMaximal}.Finite := by
  apply (Algebra.QuasiFinite.finite_primesOver (R := R) (S := S)
    (IsLocalRing.maximalIdeal R)).subset
  intro P hP
  let : P.IsMaximal := hP
  have hunder : P.under R = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal inferInstance
  exact ⟨hP.isPrime, hunder ▸ inferInstanceAs (P.LiesOver (P.under R))⟩

theorem isPrincipalIdealRing (R S : Type*) [CommRing R] [CommRing S]
    [IsLocalRing R] [IsDedekindDomain S] [Algebra R S] [Module.Finite R S] :
    IsPrincipalIdealRing S :=
  IsPrincipalIdealRing.of_finite_maximals (finite_maximalIdeals R S)

end OAI.AlgebraicGeometry.CycleClass.Thom.SemilocalPID.Constructions
