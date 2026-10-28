import OAI.AlgebraicGeometry.Resolution.Blowups.HypersurfacePointLift

/-! # Retraction Coverage -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.RetractionCoverage.Construction

noncomputable section

/-! The constructed coordinate retraction covers the original hypersurface at every prime. -/

universe u

variable {σ k R V : Type u} [Field k] [CommRing R] [CommRing V]
  [Algebra (MvPolynomial σ k) R] [Algebra k R] [IsScalarTower k (MvPolynomial σ k) R]
  (h : σ) [Algebra (MvPolynomialRetraction.Construction.coordinateLineFiber (k := k) (R := R) h) V]
  (w : V) (g : R →+* V)
  (e : (V ⧸ Ideal.span {w}) ≃ₐ[MvPolynomialRetraction.Construction.coordinateLineFiber (k := k) (R := R) h]
    MvPolynomialRetraction.Construction.coordinateLineFiber (k := k) (R := R) h)
  (he : e.toRingHom.comp ((Ideal.Quotient.mk (Ideal.span {w})).comp g) = Ideal.Quotient.mk _)

include he in
omit [IsScalarTower k (MvPolynomial σ k) R] in
/-- The specific retraction refinement used by coefficient induction retains
every original hypersurface point with its original residue-field map. -/
theorem coordinate_retraction_lifts_hypersurface_point (q : Ideal R) [q.IsPrime]
    (hq : algebraMap (MvPolynomial σ k) R (MvPolynomial.X h) ∈ q) :
    ∃ η : V →+* q.ResidueField, η.comp g = algebraMap R q.ResidueField := by
  let E := e.toRingEquiv.trans (MvPolynomialRetraction.Construction.coordinateLineFiberEquiv (k := k) (R := R) h).toRingEquiv
  have hE : E.toRingHom.comp ((Ideal.Quotient.mk (Ideal.span {w})).comp g) =
      Ideal.Quotient.mk (Ideal.span {algebraMap (MvPolynomial σ k) R (MvPolynomial.X h)}) := by
    apply RingHom.ext
    intro x
    change MvPolynomialRetraction.Construction.coordinateLineFiberEquiv h (e (Ideal.Quotient.mk (Ideal.span {w}) (g x))) = _
    rw [show e (Ideal.Quotient.mk (Ideal.span {w}) (g x)) = Ideal.Quotient.mk _ x
      from RingHom.congr_fun he x, MvPolynomialRetraction.Construction.coordinateLineFiberEquiv_mk]
  exact HypersurfacePointLift.Construction.hypersurface_isomorphism_lifts_prime_point _ w g E hE q hq

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.RetractionCoverage.Construction
