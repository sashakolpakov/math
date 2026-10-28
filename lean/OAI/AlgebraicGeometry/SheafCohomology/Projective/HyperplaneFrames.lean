/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplanePole
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CanonicalIdealFrame

/-! # Hyperplane Frames -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneFrames.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.AlgebraicGeometry _root_.CategoryTheory
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The explicit standard-chart trivialization of the coordinate-hyperplane
ideal module `O(-1)`. -/
noncomputable def coordinateHyperplaneIdealModuleTrivialization (i j : σ) :
    Invertible.Scheme.Modules.unitObj
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).toScheme ≅
      (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).restrict
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).ι := by
  letI : IsClosedImmersion (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j) :=
    SpaceHyperplane.MvPolynomial.coordinateHyperplaneι_isClosedImmersion j
  letI : QuasiCompact (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j) := inferInstance
  let U : (Proj (homogeneousSubmodule σ R)).affineOpens :=
    ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
  let r := CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j
  have hr : r ∈ (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j).ker.ideal U := by
    rw [CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_span]
    exact Ideal.mem_span_singleton_self r
  exact CanonicalIdealFrame.localIdealGeneratorIso
    (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j) U r hr
      (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_span i j)
      (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_mem_nonZeroDivisors i j)

/-- The explicit standard-chart trivialization of the coordinate-hyperplane
pole sheaf `O(1)`. -/
noncomputable def coordinateHyperplanePoleSheafTrivialization (i j : σ) :
    (HyperplanePole.MvPolynomial.coordinateHyperplanePoleSheaf (R := R) j).restrict
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).ι ≅
      Invertible.Scheme.Modules.unitObj (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i).toScheme :=
  Dual.Scheme.Modules.dualRestrictIsoOfRestrictIso
    (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    (coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneFrames.MvPolynomial
