import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoordinateSeparation
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.HypersurfaceBoundaryFiber

/-! # Transverse Coordinate Fiber -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Restrict actual boundary equations to any transverse coordinate hypersurface. -/

universe u v

variable {k R : Type u} {ι : Type v} [Field k] [CommRing R] [Algebra k R]
  {w : ι → R}

/-- An unused model coordinate cuts a hypersurface on which all the
original boundary equations still admit an explicit normal-crossing
model. The quotient is the actual hypersurface ring over the original field. -/
def Etale.BoundaryModel.Construction.EtaleBoundaryModel.transverseCoordinateFiber (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (h : M.indices) (hh : ∀ j, M.coordinate j ≠ some h) :
    Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k (R ⧸ Ideal.span {M.map (MvPolynomial.X h)}) ι
      (fun j => Ideal.Quotient.mk (Ideal.span {M.map (MvPolynomial.X h)}) (w j)) := by
  let : Algebra (MvPolynomial M.indices k) R := M.map.toAlgebra
  let : Algebra.Etale (MvPolynomial M.indices k) R := RingHom.etale_algebraMap.mp M.etale
  let : IsScalarTower k (MvPolynomial M.indices k) R :=
    IsScalarTower.of_algebraMap_eq (fun c => (M.ground c).symm)
  let A := MvPolynomialRelativeLine.Construction.coordinateLineBase (k := k) h
  let : Algebra A R := MvPolynomialRelativeLine.Construction.coordinateLineBaseAlgebra h
  let : Algebra (Polynomial A) R := MvPolynomialRelativeLine.Construction.coordinateLineAlgebra h
  let : IsScalarTower A (Polynomial A) R := MvPolynomialRelativeLine.Construction.coordinateLine_scalarTower h
  let : IsScalarTower k A R := MvPolynomialRelativeLine.Construction.coordinateLine_originalScalarTower h
  let : Algebra.Etale (Polynomial A) R := MvPolynomialRelativeLine.Construction.coordinateLine_etale h
  let v : ι → A := fun j => match M.separatedCoordinate h hh j with
    | none => 1 | some t => MvPolynomial.X t
  have he (j : ι) : w j = M.multiplier j * algebraMap A R (v j) :=
    M.separated_equation h hh j
  have hz : algebraMap (Polynomial A) R Polynomial.X = M.map (MvPolynomial.X h) :=
    MvPolynomialRelativeLine.Construction.coordinateLineMap_X h
  let N := (M.separatedCoefficientModel h hh).hypersurfaceFiberWithUnits (R := R)
    M.multiplier M.multiplierUnit
  have hw : (fun j => M.multiplier j * algebraMap A R (v j)) = w := funext fun j => (he j).symm
  change Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k (R ⧸ Ideal.span {M.map (MvPolynomial.X h)}) ι _
  have hn : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k (Blowups.Etale.HypersurfaceRetraction.Construction.etaleCoordinateFiber A R) ι
      (fun j => Ideal.Quotient.mk (Ideal.span {algebraMap (Polynomial A) R Polynomial.X})
        (M.multiplier j * algebraMap A R (v j))) := N
  rw [show (fun j => Ideal.Quotient.mk (Ideal.span {algebraMap (Polynomial A) R Polynomial.X})
      (M.multiplier j * algebraMap A R (v j))) =
      (fun j => Ideal.Quotient.mk (Ideal.span {algebraMap (Polynomial A) R Polynomial.X}) (w j)) from
    congrArg (fun t : ι → R => fun j => Ideal.Quotient.mk
      (Ideal.span {algebraMap (Polynomial A) R Polynomial.X}) (t j)) hw] at hn
  have ht := congrArg (fun z : R => Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k (R ⧸ Ideal.span {z}) ι
    (fun j => Ideal.Quotient.mk (Ideal.span {z}) (w j))) hz
  exact ht ▸ hn

end

end OAI.AlgebraicGeometry.Resolution.Blowups
