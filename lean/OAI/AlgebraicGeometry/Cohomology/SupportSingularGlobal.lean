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
import OAI.Algebra.Homology.MapExtendNaturality
import OAI.AlgebraicGeometry.Cohomology.GlobalSections
import OAI.AlgebraicTopology.Singular.GlobalRestriction
import OAI.AlgebraicTopology.Singular.RelativeCochainG

/-! # Support Singular Global -/

namespace OAI.AlgebraicGeometry.Cohomology.SupportSingularGlobal.AlgebraicTopology.Singular

noncomputable section

/-!
# Global singular restriction and relative cohomology

This file identifies restriction on global raw singular cochains with the algebraic dual of
the singular-chain inclusion of a topological pair.
-/

open _root_.CategoryTheory Limits _root_.TopologicalSpace

open _root_.AlgebraicTopology
open OAI.AlgebraicTopology.Singular

universe u v

variable (R : Type) [CommRing R] (X : TopCat.{0})

/-- The raw global singular-cochain complex, extended by zero to integer degrees. -/
def globalRawSingularCochainComplexInt : CochainComplex AddCommGrpCat ℤ :=
  (AlgebraicTopology.Singular.SheafSubdivisionCochain.globalRawSingularCochainComplex R X).extend ComplexShape.embeddingUpNat

/-- The raw global singular-cochain pushforward from a subset, extended by zero to integer
degrees. -/
def globalRawPushforwardSingularCochainComplexInt (A : Set X) :
    CochainComplex AddCommGrpCat ℤ :=
  (AlgebraicTopology.Singular.GlobalRestriction.globalRawPushforwardSingularCochainComplex R
    (AlgebraicTopology.Singular.ExcisionCoverSmall.topologicalSubsetInclusion X A)).extend ComplexShape.embeddingUpNat

/-- Raw global restriction, extended by zero to integer degrees. -/
def globalRawSingularRestrictionInt (A : Set X) :
    globalRawSingularCochainComplexInt R X ⟶
      globalRawPushforwardSingularCochainComplexInt R X A :=
  HomologicalComplex.extendMap
    (AlgebraicTopology.Singular.GlobalRestriction.globalRawSingularRestriction R (AlgebraicTopology.Singular.ExcisionCoverSmall.topologicalSubsetInclusion X A))
      ComplexShape.embeddingUpNat

end

end OAI.AlgebraicGeometry.Cohomology.SupportSingularGlobal.AlgebraicTopology.Singular
