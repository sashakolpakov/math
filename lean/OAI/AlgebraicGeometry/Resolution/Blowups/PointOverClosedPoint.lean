import Mathlib.RingTheory.Spectrum.Prime.Basic

/-! # Point Over Closed Point -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.PointOverClosedPoint.Construction

/-! A prime over a closed point has a maximal specialization over that same point. -/

theorem exists_maximal_point_over_closed_point {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (q : Ideal R) [q.IsMaximal]
    (P : PrimeSpectrum S) (hP : P.asIdeal.comap f = q) :
    ∃ Q : Ideal S, Q.IsMaximal ∧ Q.comap f = q := by
  obtain ⟨Q, hQ, hPQ⟩ := Ideal.exists_le_maximal P.asIdeal P.isPrime.ne_top
  let : Q.IsMaximal := hQ
  have hqQ : q ≤ Q.comap f := hP ▸ Ideal.comap_mono hPQ
  exact ⟨Q, hQ, ((inferInstance : q.IsMaximal).eq_of_le
    (inferInstance : (Q.comap f).IsPrime).ne_top hqQ).symm⟩

end OAI.AlgebraicGeometry.Resolution.Blowups.PointOverClosedPoint.Construction
