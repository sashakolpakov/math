import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.RetractionUnitComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoordinateLineFiber
import OAI.AlgebraicGeometry.Resolution.Blowups.MvPolynomialRetraction
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.RetractionCoverage

/-! # Coordinate Retraction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.CoordinateRetraction.Construction

noncomputable section

/-! Actual coefficient retractions retain every original boundary equation up to units. -/

universe u v

variable {k R : Type u} {ι : Type v} [Field k] [CommRing R] [Algebra k R]
  {w : ι → R}

/-- A transverse coordinate admits an actual étale retraction onto its
coefficient fiber. That fiber has the full original boundary model, and
the original ambient equations are unit multiples of its pulled-back
boundary equations. The retraction square is exact. -/
theorem exists_modeled_coordinate_retraction (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (h : M.indices) (hh : ∀ j, M.coordinate j ≠ some h) :
    letI : Algebra (MvPolynomial M.indices k) R := M.map.toAlgebra
    let H := MvPolynomialRetraction.Construction.coordinateLineFiber (k := k) (R := R) h
    Nonempty (Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k H ι (fun j => Ideal.Quotient.mk _ (w j))) ∧
    ∃ (V : Type u) (_ : CommRing V) (_ : Algebra k V) (_ : Algebra H V)
      (_ : Algebra (Polynomial H) V),
      IsScalarTower k H V ∧ IsScalarTower H (Polynomial H) V ∧
      Algebra.Etale (Polynomial H) V ∧
      ∃ g : R →ₐ[k] V, g.toRingHom.Etale ∧
        g (M.map (MvPolynomial.X h)) = algebraMap (Polynomial H) V Polynomial.X ∧
        ∃ e : (V ⧸ Ideal.span {algebraMap (Polynomial H) V Polynomial.X}) ≃ₐ[H] H,
          e.toRingHom.comp ((Ideal.Quotient.mk _).comp g.toRingHom) = Ideal.Quotient.mk _ ∧
          ∃ v : ι → V, (∀ j, IsUnit (v j)) ∧
            (∀ j, g (w j) = v j * algebraMap H V (Ideal.Quotient.mk _ (w j))) ∧
            ∀ q : PrimeSpectrum R, M.map (MvPolynomial.X h) ∈ q.asIdeal →
              ∃ Q : PrimeSpectrum V, PrimeSpectrum.comap g.toRingHom Q = q := by
  let : Algebra (MvPolynomial M.indices k) R := M.map.toAlgebra
  let : Algebra.Etale (MvPolynomial M.indices k) R := RingHom.etale_algebraMap.mp M.etale
  let : IsScalarTower k (MvPolynomial M.indices k) R :=
    IsScalarTower.of_algebraMap_eq (fun c => (M.ground c).symm)
  let H := MvPolynomialRetraction.Construction.coordinateLineFiber (k := k) (R := R) h
  have hmodel : Nonempty (Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k H ι (fun j => Ideal.Quotient.mk _ (w j))) :=
    ⟨M.coordinateLineFiberModel h hh⟩
  obtain ⟨V, cV, akV, aHV, aHPV, hkHV, hHPV, heV, g, hg, hgk, hcoord, hcoeff, e, hcomm⟩ :=
    MvPolynomialRetraction.Construction.exists_coordinate_retraction_neighborhood (k := k) (R := R) h
  let f : R →ₐ[k] V := { g with commutes' := hgk }
  let ρ : R →+* V := (algebraMap H V).comp (Ideal.Quotient.mk _)
  have hret (s : M.boundaryIndices) : g (M.map (MvPolynomial.X s.val)) = ρ (M.map (MvPolynomial.X s.val)) := by
    have hs : s.val ≠ h := by
      intro hs
      obtain ⟨j, hj⟩ := (M.mem_boundaryIndices s.val).mp s.property
      exact hh j (hj.trans (congrArg some hs))
    exact hcoeff ⟨s.val, hs⟩
  obtain ⟨v, hv, hw⟩ := M.retraction_unit_comparison g ρ hret
  have hcover (q : PrimeSpectrum R) (hq : M.map (MvPolynomial.X h) ∈ q.asIdeal) :
      ∃ Q : PrimeSpectrum V, PrimeSpectrum.comap g Q = q := by
    obtain ⟨η, hη⟩ := Coordinate.RetractionCoverage.Construction.coordinate_retraction_lifts_hypersurface_point h
      (algebraMap (Polynomial H) V Polynomial.X) g e hcomm q.asIdeal hq
    refine ⟨⟨RingHom.ker η, RingHom.ker_isPrime η⟩, PrimeSpectrum.ext ?_⟩
    ext x
    change η (g x) = 0 ↔ x ∈ q.asIdeal
    rw [show η (g x) = algebraMap R q.asIdeal.ResidueField x from RingHom.congr_fun hη x]
    exact Ideal.algebraMap_residueField_eq_zero
  exact ⟨hmodel, V, cV, akV, aHV, aHPV, hkHV, hHPV, heV, f, hg, hcoord, e, hcomm, v, hv, hw, hcover⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.CoordinateRetraction.Construction
