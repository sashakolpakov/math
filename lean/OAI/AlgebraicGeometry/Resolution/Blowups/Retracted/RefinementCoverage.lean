import OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.CoefficientRefinementTransport
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DifferentialMap

/-! # Refinement Coverage -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.RefinementCoverage.Construction

noncomputable section

/-! Actual point coverage by refined coefficient charts and termination off the hypersurface. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

/-- A covering family on the retained hypersurface lifts to a covering
family over every point of that hypersurface in the original ambient scheme.
The statement uses the actual retraction squares, including nonclosed points. -/
theorem retracted_coefficient_cover_lifts
    {H R : Type u} [CommRing H] [CommRing R] {ι : Type u}
    (z : R) (e : (R ⧸ Ideal.span {z}) ≃+* H)
    (B V : ι → CommRingCat.{u}) (φ : ∀ i, H →+* B i) (f : ∀ i, R →+* V i)
    (e' : ∀ i, (V i ⧸ Ideal.span {f i z}) ≃+* B i)
    (hcomm : ∀ i, (e' i).toRingHom.comp ((Ideal.Quotient.mk (Ideal.span {f i z})).comp (f i)) =
      (φ i).comp (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {z}))))
    (hcover : ∀ p : PrimeSpectrum H, ∃ i, ∃ q : PrimeSpectrum (B i),
      PrimeSpectrum.comap (φ i) q = p)
    (p : PrimeSpectrum R) (hz : z ∈ p.asIdeal) :
    ∃ i, ∃ q : PrimeSpectrum (V i), PrimeSpectrum.comap (f i) q = p := by
  let ρ := e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {z}))
  have hsurj : Function.Surjective ρ := e.surjective.comp Ideal.Quotient.mk_surjective
  have hker : RingHom.ker ρ ≤ p.asIdeal := by
    intro x hx
    change e (Ideal.Quotient.mk (Ideal.span {z}) x) = 0 at hx
    have hzero : Ideal.Quotient.mk (Ideal.span {z}) x = 0 :=
      e.injective (by simpa only [map_zero] using hx)
    exact ((Ideal.span_singleton_le_iff_mem p.asIdeal).mpr hz)
      (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  let P : PrimeSpectrum H := ⟨p.asIdeal.map ρ, Ideal.map_isPrime_of_surjective hsurj hker⟩
  have hP : P.asIdeal.comap ρ = p.asIdeal := by
    change (p.asIdeal.map ρ).comap ρ = p.asIdeal
    rw [Ideal.comap_map_of_surjective ρ hsurj, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hker]
  obtain ⟨i, q, hq⟩ := hcover P
  let ρ' := (e' i).toRingHom.comp (Ideal.Quotient.mk (Ideal.span {f i z}))
  refine ⟨i, PrimeSpectrum.comap ρ' q, ?_⟩
  apply PrimeSpectrum.ext
  change (q.asIdeal.comap ρ').comap (f i) = p.asIdeal
  rw [Ideal.comap_comap]
  change q.asIdeal.comap ((e' i).toRingHom.comp
    ((Ideal.Quotient.mk (Ideal.span {f i z})).comp (f i))) = _
  rw [hcomm i, ← Ideal.comap_comap]
  have hqI : q.asIdeal.comap (φ i) = P.asIdeal := congrArg PrimeSpectrum.asIdeal hq
  rw [hqI]
  exact hP

variable (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]
  [Algebra.Smooth k R]

/-- The complementary actual principal open is terminal when the chosen
hypersurface equation belongs to the maximal-contact differential ideal. -/
theorem relative_hypersurface_complement_terminal
    (J : Ideal R) (z : R) (n : ℕ) (hz : z ∈ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n) :
    Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J.map (algebraMap R (Localization.Away z))) n = ⊤ := by
  let : Algebra.Etale R (Localization.Away z) := Algebra.Etale.of_isLocalizationAway z
  rw [← Blowups.Smooth.DifferentialNaturality.Construction.smooth_iteratedRelativeDifferentialIdeal_baseChange k J n]
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hz)
    (IsLocalization.Away.algebraMap_isUnit z)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Retracted.RefinementCoverage.Construction
