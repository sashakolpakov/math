import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.OpenDimension
import Mathlib.RingTheory.Unramified.LocalStructure

/-! # Dimension -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Etale.Dimension.Construction

noncomputable section

/-! Actual quasi-finite and étale chart maps do not increase Krull dimension. -/

universe u

/-- Incomparable primes in a quasi-finite fiber force every strict chain
of primes upstairs to contract to a strict chain downstairs. -/
theorem ringKrullDim_le_of_quasiFinite (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.QuasiFinite R S] : ringKrullDim S ≤ ringKrullDim R := by
  apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
  intro p q hpq
  refine lt_of_le_of_ne (Ideal.comap_mono hpq.le) ?_
  intro heq
  apply hpq.ne
  apply PrimeSpectrum.ext
  exact Algebra.QuasiFinite.eq_of_le_of_under_eq (R := R) p.asIdeal q.asIdeal hpq.le
    (congrArg PrimeSpectrum.asIdeal heq)

/-- An explicit étale ring map retains any finite dimension bound without
requiring the map to be an open immersion or the rings to be integral. -/
theorem ringKrullDim_le_of_etale {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Etale) : ringKrullDim S ≤ ringKrullDim R := by
  let : Algebra R S := f.toAlgebra
  let : Algebra.Etale R S := RingHom.etale_algebraMap.mp hf
  exact ringKrullDim_le_of_quasiFinite R S

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Etale.Dimension.Construction
