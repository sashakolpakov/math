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
import OAI.AlgebraicGeometry.ComplexPoint.AnalyticSheaf

/-! # Analytic Sheaf On -/

namespace OAI.AlgebraicGeometry.ComplexPoint

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Holomorphic functions on complex points

-/

open _root_.CategoryTheory _root_.TopologicalSpace _root_.Topology
open scoped ContDiff _root_.Manifold

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- A section of the holomorphic-function sheaf is an analytic map to `ℂ` in the charted-space
structure on complex points. -/
lemma Basic.ComplexSchemePoint.holomorphicFunctionSheaf_section_analytic [SmoothOfRelativeDimension d X.hom]
    {U : (Opens (TopCat.of (Basic.ComplexSchemePoint X)))ᵒᵖ}
    (s : (Basic.ComplexSchemePoint.holomorphicFunctionSheaf X d).presheaf.obj U) :
    ContMDiff 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ω s.1 :=
  (contDiffWithinAt_localInvariantProp ω).section_spec _ _ _ _

end

end OAI.AlgebraicGeometry.ComplexPoint
