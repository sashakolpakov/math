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
import Mathlib.Topology.KrullDimension
import OAI.Topology.Foundations.KrullDimension

/-! # Basic -/

namespace OAI.Topology.Dimension.Basic.TopologicalSpace

noncomputable section

open _root_.TopologicalSpace

/-!
# The dimension of an irreducible topological space
-/

/-- Let `X` be an irreducible topological space. Its dimension is the supremum of the lengths of
strict chains of nonempty irreducible closed subsets, converted to a natural number. A chain of
`r+1` subsets has length `r`. This conversion returns `0` when the Krull dimension is infinite;
irreducibility excludes the empty-space case. -/
@[nolint unusedArguments]
def dim (X : Type*) [TopologicalSpace X] [IrreducibleSpace X] : ℕ :=
  ((topologicalKrullDim X).unbotD 0).toNat

end

end OAI.Topology.Dimension.Basic.TopologicalSpace
