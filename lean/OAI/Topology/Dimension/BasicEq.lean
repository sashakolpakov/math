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
import OAI.Topology.Dimension.Basic
import OAI.Topology.Foundations.KrullDimension

/-! # Basic Eq -/

namespace OAI.Topology.Dimension.BasicEq.TopologicalSpace

noncomputable section

open _root_.TopologicalSpace

/-!
# The dimension of an irreducible topological space

-/

attribute [local instance] specializationOrder in
/-- On a sober space, and in particular on a scheme, the dimension counts chains of points under
specialisation. -/
lemma dim_eq_krullDim (X : Type*) [TopologicalSpace X] [IrreducibleSpace X] [T0Space X]
    [QuasiSober X] : Basic.TopologicalSpace.dim X = ((Order.krullDim X).unbotD 0).toNat := by
  rw [Basic.TopologicalSpace.dim, Foundations.KrullDimension.topologicalKrullDim_eq_krullDim]

end

end OAI.Topology.Dimension.BasicEq.TopologicalSpace
