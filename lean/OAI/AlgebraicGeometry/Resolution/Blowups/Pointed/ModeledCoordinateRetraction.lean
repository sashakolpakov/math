import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.CoordinateRetraction

/-! # Modeled Coordinate Retraction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.ModeledCoordinateRetraction.Construction

noncomputable section

/-! A specified hypersurface point remains on the actual retracted normal fiber. -/

universe u v

variable {k R : Type u} {ι : Type v} [Field k] [CommRing R] [Algebra k R]
  {w : ι → R}

theorem exists_pointed_modeled_coordinate_retraction (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (h : M.indices) (hh : ∀ j, M.coordinate j ≠ some h)
    (z : R) (hz : M.map (MvPolynomial.X h) = z) (q : PrimeSpectrum R) (hzq : z ∈ q.asIdeal) :
    letI : Algebra (MvPolynomial M.indices k) R := M.map.toAlgebra
    let H := MvPolynomialRetraction.Construction.coordinateLineFiber (k := k) (R := R) h
    ∃ (V : Type u) (_ : CommRing V) (_ : Algebra k V) (_ : Algebra H V)
      (_ : Algebra (Polynomial H) V),
      IsScalarTower k H V ∧ IsScalarTower H (Polynomial H) V ∧ Algebra.Etale (Polynomial H) V ∧
      ∃ g : R →ₐ[k] V, g.toRingHom.Etale ∧
        g z = algebraMap (Polynomial H) V Polynomial.X ∧
        ∃ e : (V ⧸ Ideal.span {algebraMap (Polynomial H) V Polynomial.X}) ≃ₐ[H] H,
          e.toRingHom.comp ((Ideal.Quotient.mk _).comp g.toRingHom) = Ideal.Quotient.mk _ ∧
          ∃ u : ι → V, (∀ j, IsUnit (u j)) ∧
            (∀ j, g (w j) = u j * algebraMap H V (Ideal.Quotient.mk _ (w j))) ∧
            ∃ Q : PrimeSpectrum V, PrimeSpectrum.comap g.toRingHom Q = q ∧
              algebraMap (Polynomial H) V Polynomial.X ∈ Q.asIdeal := by
  let : Algebra (MvPolynomial M.indices k) R := M.map.toAlgebra
  let H := MvPolynomialRetraction.Construction.coordinateLineFiber (k := k) (R := R) h
  obtain ⟨_, V, cV, akV, aHV, aHPV, hkHV, hHPV, heV, g, hg, hnormal, e, hcomm, u, hu, hw, hcover⟩ :=
    Modeled.CoordinateRetraction.Construction.exists_modeled_coordinate_retraction M h hh
  have hn : g z = algebraMap (Polynomial H) V Polynomial.X := by
    rw [← hz]
    exact hnormal
  obtain ⟨Q, hQ⟩ := hcover q (hz.symm ▸ hzq)
  have hQI : Q.asIdeal.comap g.toRingHom = q.asIdeal := congrArg PrimeSpectrum.asIdeal hQ
  have hzQ : algebraMap (Polynomial H) V Polynomial.X ∈ Q.asIdeal := by
    rw [← hn]
    change z ∈ Q.asIdeal.comap g.toRingHom
    rw [hQI]
    exact hzq
  exact ⟨V, cV, akV, aHV, aHPV, hkHV, hHPV, heV, g, hg, hn, e, hcomm, u, hu, hw, Q, hQ, hzQ⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Pointed.ModeledCoordinateRetraction.Construction
