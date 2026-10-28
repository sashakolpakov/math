/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
This file has been modified.
-/
import OAI.AlgebraicGeometry.ComplexPoint.BasicNe
import OAI.AlgebraicTopology.Singular.SheafCochainAt
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.Embedding.Extend
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import OAI.CategoryTheory.ConcreteCategory.Notation
import OAI.AlgebraicGeometry.ComplexPoint.Manifold
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # Singular Comparison -/

namespace OAI.AlgebraicGeometry.Cohomology.SingularComparison.ComplexPoint

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Singular cochains on smooth complex-point spaces

The algebraic coordinate charts on a smooth complex scheme give a basis of open contractible
neighborhoods. Singular chains on each such neighborhood are exact in positive degree. Duality
therefore supplies local primitives for singular cochains. Together with the explicit degree-zero
calculation, this proves that the constant-sheaf-to-singular-cochain map is a quasi-isomorphism.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- The constant-to-singular-cochain comparison on a smooth complex-point space is a
quasi-isomorphism in positive degrees. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochain_quasiIsoAt_succ
    [IsIntegral X.left] [Smooth X.hom]
    (R : Type) [CommRing R] (n : ℕ) :
    QuasiIsoAt
      (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainSheafComplex R
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) (n + 1) := by
  apply AlgebraicTopology.Singular.SheafCochainAt.constantsToSingularCochainSheafComplex_quasiIsoAt_succ_of_contractibleOpenBasis
  exact fun x U hxU ↦ ComplexPoint.Basic.ComplexSchemePoint.exists_contractibleOpen_le X x U hxU

/-- The constant-to-singular-cochain comparison on a smooth complex-point space is a
quasi-isomorphism in degree zero. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochain_quasiIsoAt_zero
    [IsIntegral X.left] [Smooth X.hom]
    (R : Type) [CommRing R] :
    QuasiIsoAt
      (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainSheafComplex R
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) 0 := by
  let : LocallyPathConnectedSpace (ComplexPoint.Basic.ComplexSchemePoint X) :=
    ComplexPoint.Basic.ComplexSchemePoint.locallyPathConnectedSpace X
  exact
    AlgebraicTopology.Singular.SheafCochainAt.constantsToSingularCochainSheafComplex_quasiIsoAt_zero
      R (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))

/-- On the analytic space of a smooth complex scheme, the constant sheaf is resolved by the
sheafified singular-cochain complex. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochain_quasiIso
    [IsIntegral X.left] [Smooth X.hom]
    (R : Type) [CommRing R] :
    QuasiIso
      (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainSheafComplex R
        (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) := by
  refine ⟨fun n ↦ ?_⟩
  cases n with
  | zero => exact ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochain_quasiIsoAt_zero X R
  | succ n => exact ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochain_quasiIsoAt_succ X R n

/-- The sheafified singular-cochain complex, extended by zero to integer degrees. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt (R : Type) [CommRing R] :
    CochainComplex
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) ℤ :=
  (AlgebraicTopology.Singular.SheafCochain.singularCochainSheafComplex R
    (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))).extend ComplexShape.embeddingUpNat

instance (R : Type) [CommRing R] :
    CochainComplex.IsStrictlyGE (ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R) 0 := by
  unfold ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt
  infer_instance

/-- The constant coefficient sheaf complex, extended by zero to integer degrees. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantCoefficientSheafComplexInt (R : Type) [CommRing R] :
    CochainComplex
      (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) ℤ :=
  ((CochainComplex.single₀
    (TopCat.Sheaf AddCommGrpCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))).obj
      𝓒(↧(ComplexPoint.Basic.ComplexSchemePoint X); R)).extend ComplexShape.embeddingUpNat

/-- The constant-to-singular comparison, extended by zero to integer degrees. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt (R : Type) [CommRing R] :
    ComplexPoint.Basic.ComplexSchemePoint.constantCoefficientSheafComplexInt X R ⟶
      ComplexPoint.Basic.ComplexSchemePoint.singularCochainSheafComplexInt X R :=
  HomologicalComplex.extendMap
    (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainSheafComplex R
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) ComplexShape.embeddingUpNat

/-- The integer-indexed constant-to-singular comparison remains a quasi-isomorphism. -/
lemma _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt_quasiIso
    [IsIntegral X.left] [Smooth X.hom]
    (R : Type) [CommRing R] :
    QuasiIso (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochainComplexInt X R) := by
  exact (HomologicalComplex.quasiIso_extendMap_iff
    (AlgebraicTopology.Singular.SheafCochain.constantsToSingularCochainSheafComplex R
      (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X))) ComplexShape.embeddingUpNat).mpr
        (ComplexPoint.Basic.ComplexSchemePoint.constantsToSingularCochain_quasiIso X R)

end

end OAI.AlgebraicGeometry.Cohomology.SingularComparison.ComplexPoint
