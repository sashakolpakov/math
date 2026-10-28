/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneIdeal
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Dual

/-! # Hyperplane Pole -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplanePole.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.AlgebraicGeometry _root_.CategoryTheory
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The dual of the coordinate-hyperplane ideal module, giving the concrete
model of `O(1)` on polynomial projective space. -/
noncomputable def coordinateHyperplanePoleSheaf (j : σ) :
    (Proj (homogeneousSubmodule σ R)).Modules :=
  Dual.Scheme.Modules.dualObj
    (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))

/-- The canonical coordinate section `O → O(1)`, obtained by dualizing the inclusion of
the coordinate-hyperplane ideal. -/
noncomputable def coordinateHyperplanePoleUnitHom (j : σ) :
    Invertible.Scheme.Modules.unitObj (Proj (homogeneousSubmodule σ R)) ⟶
      coordinateHyperplanePoleSheaf (R := R) j :=
  (Dual.Scheme.Modules.dualUnitObjIso
      (X := Proj (homogeneousSubmodule σ R))).inv ≫
    Dual.Scheme.Modules.dualMapObj
      (IdealModule.idealModuleToUnit
        (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))

/-- The canonical global coordinate section of the concrete `O(1)`. -/
noncomputable def coordinateHyperplanePoleSection (j : σ) :
    Γ(coordinateHyperplanePoleSheaf (R := R) j,
      (⊤ : (Proj (homogeneousSubmodule σ R)).Opens)) :=
  (coordinateHyperplanePoleUnitHom (R := R) j).val.app (.op ⊤)
    (show (Proj (homogeneousSubmodule σ R)).presheaf.obj (.op ⊤) from 1)

/-- The concrete `O(1)` on polynomial projective space is invertible. -/
theorem coordinateHyperplanePoleSheaf_isInvertible (j : σ) :
    Invertible.Scheme.Modules.IsInvertible (coordinateHyperplanePoleSheaf (R := R) j) :=
  (HyperplaneIdeal.MvPolynomial.coordinateHyperplaneIdealModule_isInvertible (R := R) j).dual

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplanePole.MvPolynomial
