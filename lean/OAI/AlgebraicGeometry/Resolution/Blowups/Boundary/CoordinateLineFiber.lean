import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.CoordinateSeparation
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.HypersurfaceBoundaryFiber
import OAI.AlgebraicGeometry.Resolution.Blowups.MvPolynomialRetraction

/-! # Coordinate Line Fiber -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Boundary models on the precise coefficient-fiber presentation used by retraction. -/

universe u v

variable {k R : Type u} {ι : Type v} [Field k] [CommRing R] [Algebra k R]
  {w : ι → R}

def Etale.BoundaryModel.Construction.EtaleBoundaryModel.coordinateLineFiberModel (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w)
    (h : M.indices) (hh : ∀ j, M.coordinate j ≠ some h) :
    letI : Algebra (MvPolynomial M.indices k) R := M.map.toAlgebra
    Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k (MvPolynomialRetraction.Construction.coordinateLineFiber (k := k) (R := R) h) ι
      (fun j => Ideal.Quotient.mk _ (w j)) := by
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
  have he : (fun j => M.multiplier j * algebraMap A R (v j)) = w :=
    funext fun j => (M.separated_equation h hh j).symm
  let N := (M.separatedCoefficientModel h hh).hypersurfaceFiberWithUnits (R := R)
    M.multiplier M.multiplierUnit
  have ht := congrArg (fun t : ι → R => Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k (Blowups.Etale.HypersurfaceRetraction.Construction.etaleCoordinateFiber A R) ι
    (fun j => Ideal.Quotient.mk (Ideal.span {algebraMap (Polynomial A) R Polynomial.X}) (t j))) he
  exact ht ▸ N

end

end OAI.AlgebraicGeometry.Resolution.Blowups
