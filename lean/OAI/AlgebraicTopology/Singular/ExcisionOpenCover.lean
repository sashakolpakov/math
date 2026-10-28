/-
Copyright 2026 Paul Lezeau and The Formal Conjectures Authors.

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
import OAI.AlgebraicTopology.Singular.CoverSmallQuasiIso
import OAI.AlgebraicTopology.Singular.SubdivisionAffineRelativeMesh
import OAI.AlgebraicTopology.Singular.SubdivisionAffineSupport

/-! # Excision Open Cover -/

namespace OAI.AlgebraicTopology.Singular.ExcisionOpenCover

noncomputable section

/-!

# Small-chain approximation for open covers

This file assembles the geometric affine-mesh theorem, the exact permutation-ancestry expansion,
the adaptive quasi-isomorphism argument, and projectivity. The result is the classical
small-singular-chain theorem for every open cover, with no additional hypothesis.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set

variable {ι : Type} (X : TopCat) (U : ι → Set X)

/-- Classical small-chain approximation: the inclusion of chains subordinate to an open cover is
a chain-homotopy equivalence for integral singular chains. -/
theorem coverSmallChainApproximation_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomologicalComplex.homotopyEquivalences AddCommGrpCat (ComplexShape.down ℕ)
      (ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U) :=
  CoverSmallQuasiIso.coverSmallChainApproximation_of_eventuallySmall X U
    (SubdivisionAffineSupport.coverSmallAffineSubdivisionEventuallySmall_of_openCover X U hUopen hUcover)

/-- A selected chain-homotopy equivalence witnessing small-chain approximation. -/
noncomputable def coverSmallChainHomotopyEquiv_of_openCover
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    HomotopyEquiv (ExcisionCoverSmall.CoverSmallIntegralSingularChainComplex X U)
      (ExcisionCoverSmall.IntegralSingularChainComplexObj X) :=
  (coverSmallChainApproximation_of_openCover X U hUopen hUcover).choose

theorem coverSmallChainHomotopyEquiv_of_openCover_hom
    (hUopen : ∀ i, IsOpen (U i)) (hUcover : ⋃ i, U i = Set.univ) :
    (coverSmallChainHomotopyEquiv_of_openCover X U hUopen hUcover).hom =
      ExcisionCoverSmall.coverSmallIntegralSingularChainInclusion X U :=
  (coverSmallChainApproximation_of_openCover X U hUopen hUcover).choose_spec

end

end OAI.AlgebraicTopology.Singular.ExcisionOpenCover
