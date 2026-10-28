/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.ComplexPoint.Manifold
import OAI.AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator
import OAI.AlgebraicTopology.LocalHomology.EuclideanVanishing
import OAI.AlgebraicTopology.Singular.SheafChainStalk

/-! # Local Homology Vanishing -/

namespace OAI.AlgebraicGeometry.ComplexPoint.LocalHomologyVanishing.AlgebraicTopology.Singular

noncomputable section

/-!
# Local homology concentration on a smooth complex scheme

The compressed-chart map is an isomorphism in every local-homology degree, by
neighborhood excision. Euclidean local homology vanishing therefore proves concentration
in real dimension `2*d`, and stalk exactness gives the corresponding homology-sheaf
vanishing.
-/

open _root_.CategoryTheory Limits _root_.TopologicalSpace

open _root_.AlgebraicTopology
open OAI.AlgebraicTopology.Singular

/-- Complex coordinate space has local homology only in twice its complex dimension. -/
theorem standardComplexLocalHomology_isZero_of_ne (d n : ℕ) (hn : n ≠ 2 * d) :
    IsZero (AlgebraicTopology.Singular.Cohomology.RelativeHomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℂ d) n) :=
  (AlgebraicTopology.LocalHomology.EuclideanVanishing.Singular.standardLocalHomology_isZero_of_ne (d * 2) n (by omega)).of_iso
    ((AlgebraicTopology.Singular.Cohomology.relativeHomologyFunctor ℚ n).mapIso (AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexRealPairIso d))

end

end OAI.AlgebraicGeometry.ComplexPoint.LocalHomologyVanishing.AlgebraicTopology.Singular
