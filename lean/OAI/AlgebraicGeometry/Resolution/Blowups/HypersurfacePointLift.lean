import OAI.AlgebraicGeometry.Resolution.Blowups.MvPolynomialRetraction
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Hypersurface Point Lift -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfacePointLift.Construction

noncomputable section

/-! A refinement inducing the hypersurface isomorphism covers every point of that hypersurface. -/

variable {R V L : Type*} [CommRing R] [CommRing V] [CommRing L]
  (z : R) (w : V) (g : R →+* V)
  (e : (V ⧸ Ideal.span {w}) ≃+* (R ⧸ Ideal.span {z}))
  (he : e.toRingHom.comp ((Ideal.Quotient.mk (Ideal.span {w})).comp g) =
    Ideal.Quotient.mk (Ideal.span {z}))

include he in
/-- Every ring-valued point of the original hypersurface lifts through the
actual ambient refinement, with its entire original map retained. -/
theorem hypersurface_isomorphism_lifts_point (p : R →+* L) (hp : p z = 0) :
    ∃ η : V →+* L, η.comp g = p := by
  let pbar : (R ⧸ Ideal.span {z}) →+* L := Ideal.Quotient.lift _ p (by
    intro x hx
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp hx
    rw [hs, map_mul, hp, zero_mul (p s)])
  refine ⟨pbar.comp (e.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {w}))), ?_⟩
  apply RingHom.ext
  intro x
  have hx := congrArg pbar (RingHom.congr_fun he x)
  exact hx

include he in
/-- In particular, every prime point on the hypersurface lifts with the same
residue-field map from the original ambient ring. -/
theorem hypersurface_isomorphism_lifts_prime_point (q : Ideal R) [q.IsPrime] (hzq : z ∈ q) :
    ∃ η : V →+* q.ResidueField, η.comp g = algebraMap R q.ResidueField :=
  hypersurface_isomorphism_lifts_point z w g e he (algebraMap R q.ResidueField)
    (Ideal.algebraMap_residueField_eq_zero.mpr hzq)

include he in
/-- The induced spectrum map covers the whole original hypersurface. -/
theorem hypersurface_isomorphism_covers_primes (q : Ideal R) [q.IsPrime] (hzq : z ∈ q) :
    ∃ Q : Ideal V, Q.IsPrime ∧ Q.comap g = q := by
  obtain ⟨η, hη⟩ := hypersurface_isomorphism_lifts_prime_point z w g e he q hzq
  refine ⟨RingHom.ker η, RingHom.ker_isPrime η, ?_⟩
  ext x
  change η (g x) = 0 ↔ x ∈ q
  rw [show η (g x) = algebraMap R q.ResidueField x from RingHom.congr_fun hη x]
  exact Ideal.algebraMap_residueField_eq_zero

end

end OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfacePointLift.Construction
