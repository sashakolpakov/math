/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.Smooth.SingularLocusDimension
import OAI.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Analytification -/

namespace OAI.AlgebraicGeometry

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Complex points of the smooth decomposition

The finite algebraic decomposition induces a partition of complex-point sets into the images of
smooth complex schemes. The images are analytically locally closed, and the lifting assertion
follows from the equivalence between complex points and closed scheme points.

Analytic triangulation, homology-dimension theorems, and frontier conditions are outside the
scope of this file.
-/

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

variable (X : Over (Spec ↧ℂ)) {Y : Over (Spec ↧ℂ)}

variable [LocallyOfFiniteType X.hom] [NoetherianSpace X.left]

instance ComplexPoint.Basic.ComplexSchemePoint.reducedClosedSmoothPiece_locallyOfFiniteType (T : Closeds X.left) :
    LocallyOfFiniteType (Over.mk (Stratification.BasicLe.reducedClosedSmoothPieceι X.hom T ≫ X.hom)).hom := by
  change LocallyOfFiniteType (Stratification.BasicLe.reducedClosedSmoothPieceι X.hom T ≫ X.hom)
  infer_instance

end

end OAI.AlgebraicGeometry
