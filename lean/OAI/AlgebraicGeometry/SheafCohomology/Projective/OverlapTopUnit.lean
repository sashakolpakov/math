/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions
import OAI.AlgebraicGeometry.SheafCohomology.Projective.OpenFrames

/-! # Overlap Top Unit -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.OverlapTopUnit.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The overlap transition unit, transported to the open subscheme's top ring. -/
def coordinateOpenTransitionTopUnit (i k : σ) :
    Γ((CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme, ⊤)ˣ :=
  Units.map (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).topIso.inv.hom.toMonoidHom
    (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k)

@[simp]
theorem coordinateOpenTransitionTopUnit_coe (i k : σ) :
    (coordinateOpenTransitionTopUnit (R := R) i k :
      Γ((CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k).toScheme, ⊤)) =
    OpenFrames.Scheme.Modules.openTopSection (CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)
      (CoordinateExtensions.MvPolynomial.coordinateOpenTransitionUnit (R := R) i k :
        Γ(Proj (homogeneousSubmodule σ R), CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := R) i k)) := rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.OverlapTopUnit.MvPolynomial
