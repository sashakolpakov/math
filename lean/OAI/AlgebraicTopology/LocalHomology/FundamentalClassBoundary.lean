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
import OAI.AlgebraicTopology.LocalHomology.FundamentalClass

/-! # Fundamental Class Boundary -/

namespace OAI.AlgebraicTopology.LocalHomology.FundamentalClassBoundary.Singular

noncomputable section

/-!
# A standard local fundamental cycle

-/

open _root_.CategoryTheory Limits
open scoped Simplicial

variable (R : Type) [CommRing R]

/-- The alternating sum of the faces of the standard affine `(n + 1)`-simplex, regarded as a
chain in punctured Euclidean space. -/
def standardSubspaceBoundaryChain (n : ℕ) :
    ModuleCat.of ℚ ℚ ⟶
      ((Singular.Cohomology.chainPairFunctor ℚ).obj (FundamentalClass.Singular.puncturedPair ℝ (n + 1))).left.X n :=
  ∑ i : Fin (n + 2), (-1) ^ i.val • FundamentalClass.Singular.standardSubspaceFaceChain ℚ n i

lemma standardLocalCycle_inclusion (d : ℕ) :
    FundamentalClass.Singular.standardLocalCycle R d ≫ (FundamentalClass.Singular.standardLocalRelativeChainComplex R d).iCycles d =
      FundamentalClass.Singular.standardLocalChain R d :=
  (FundamentalClass.Singular.standardLocalRelativeChainComplex R d).liftCycles_i (FundamentalClass.Singular.standardLocalChain R d)
    ((ComplexShape.down ℕ).next d) rfl (FundamentalClass.Singular.standardLocalChain_boundary R d)

end

end OAI.AlgebraicTopology.LocalHomology.FundamentalClassBoundary.Singular
