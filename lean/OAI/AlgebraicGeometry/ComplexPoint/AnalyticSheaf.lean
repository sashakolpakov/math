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
import OAI.AlgebraicGeometry.ComplexPoint.Manifold
import Mathlib.Geometry.Manifold.Algebra.SmoothFunctions
import Mathlib.Geometry.Manifold.Sheaf.Basic

/-! # Analytic Sheaf -/

namespace OAI.AlgebraicGeometry.ComplexPoint

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Holomorphic functions on complex points

For a complex scheme smooth of relative dimension `d`, the algebraic étale charts constructed in
`ComplexPoint.SmoothCoordinates` give a canonical charted-space structure on its complex points.
This file defines its sheaf of holomorphic functions: a section is a complex-valued function
which is complex analytic in those charts. Mathlib expresses complex analyticity as manifold
differentiability of order `ω`.

The sheaf and its ring operations are built by the local-predicate sheaf machinery.
-/

open _root_.CategoryTheory _root_.TopologicalSpace _root_.Topology
open scoped ContDiff _root_.Manifold

variable (X : Over (Spec ↧ℂ)) (d : ℕ)

/-- Let `X` be a smooth scheme over `ℂ` of relative dimension `d`. On its analytic space `X(ℂ)`,
this sheaf assigns to an open `U` the complex-valued functions on `U` that are analytic in the
chosen étale coordinate charts. Restriction is restriction of functions; the values here are
sets. -/
def Basic.ComplexSchemePoint.holomorphicFunctionSheafToTypes [SmoothOfRelativeDimension d X.hom] :
    TopCat.Sheaf (Type) (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) :=
  (contDiffWithinAt_localInvariantProp (I := 𝓘(ℂ, Fin d → ℂ))
    (I' := 𝓘(ℂ)) ω).sheaf (ComplexPoint.Basic.ComplexSchemePoint X) ℂ

instance Basic.ComplexSchemePoint.holomorphicFunctionSheafToTypes.commRing [SmoothOfRelativeDimension d X.hom]
    (U : (Opens (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)))ᵒᵖ) :
    CommRing ((ComplexPoint.Basic.ComplexSchemePoint.holomorphicFunctionSheafToTypes X d).presheaf.obj U) :=
  inferInstanceAs <| CommRing
    C^ω⟮𝓘(ℂ, Fin d → ℂ), (Opposite.unop U : Opens (ComplexPoint.Basic.ComplexSchemePoint X)); ℂ⟯

/-- Let `X` be a smooth scheme over `ℂ` of relative dimension `d`. This presheaf of commutative
rings on the analytic space `X(ℂ)` assigns to each open `U` the ring of holomorphic functions `U
→ ℂ`, with pointwise operations and restriction of functions. -/
def Basic.ComplexSchemePoint.holomorphicFunctionPresheaf [SmoothOfRelativeDimension d X.hom] :
    TopCat.Presheaf CommRingCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) where
  obj U := CommRingCat.of
    ((ComplexPoint.Basic.ComplexSchemePoint.holomorphicFunctionSheafToTypes X d).presheaf.obj U)
  map h := CommRingCat.ofHom <|
    ContMDiffMap.restrictRingHom 𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ) ℂ <|
      CategoryTheory.leOfHom h.unop
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Let `X` be a smooth scheme over `ℂ` of relative dimension `d`. This is the sheaf of commutative
rings `𝒪` on `X(ℂ)`: its sections on an analytic open `U` are functions `U → ℂ` that are
analytic in the chosen étale charts, with pointwise ring operations. -/
def Basic.ComplexSchemePoint.holomorphicFunctionSheaf [SmoothOfRelativeDimension d X.hom] :
    TopCat.Sheaf CommRingCat (TopCat.of (ComplexPoint.Basic.ComplexSchemePoint X)) where
  obj := ComplexPoint.Basic.ComplexSchemePoint.holomorphicFunctionPresheaf X d
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget CommRingCat)]
    exact (ComplexPoint.Basic.ComplexSchemePoint.holomorphicFunctionSheafToTypes X d).property

end

end OAI.AlgebraicGeometry.ComplexPoint
