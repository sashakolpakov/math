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
import OAI.AlgebraicTopology.Singular.SubdivisionBasic

/-! # Subdivision Barycentric Chains -/

namespace OAI.AlgebraicTopology.Singular.SubdivisionBarycentricChains

noncomputable section

/-!

# Low-dimensional barycentric fundamental chains

This file constructs the first components of the barycentric subdivision chain operator.
The construction starts from the vertex of `sd Δ[0]` represented by the singleton chain and
uses Yoneda naturality to associate a subdivided vertex to every vertex of a simplicial set.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits PartialOrder Simplicial

/-- A singleton, regarded as a nonempty finite chain. -/
noncomputable def nonemptyFiniteChainSingleton
    {X : Type*} [LinearOrder X] (x : X) : NonemptyFiniteChains X where
  finset := {x}
  comparable := by simp

@[simp]
theorem nonemptyFiniteChainSingleton_finset
    {X : Type*} [LinearOrder X] (x : X) :
    (nonemptyFiniteChainSingleton x).finset = {x} :=
  rfl

/-- A specified nonempty finset in a linear order, regarded as a finite chain. -/
noncomputable def nonemptyFiniteChainOfFinset
    {X : Type*} [LinearOrder X] (s : Finset X) (hs : s.Nonempty) :
    NonemptyFiniteChains X where
  finset := s
  nonempty := hs
  comparable a b := le_total a b

/-- The vertex of the subdivision model of `Δ[0]` represented by its singleton vertex chain. -/
noncomputable def subdividedZeroSimplexVertex :
    (SimplexCategory.sd.{0}.obj (SimplexCategory.mk 0)).obj
      (Opposite.op (SimplexCategory.mk 0)) :=
  ComposableArrows.mk₀ (nonemptyFiniteChainSingleton (ULift.up (0 : Fin 1)))

/-- The corresponding vertex of Mathlib's left-Kan-extension model `sd Δ[0]`. -/
noncomputable def subdividedStandardZeroVertex :
    (SSet.sd.obj (Δ[0] : SSet.{0})).obj
      (Opposite.op (SimplexCategory.mk 0)) :=
  SSet.stdSimplex.sdIso.inv.app (SimplexCategory.mk 0) |>.app _
    subdividedZeroSimplexVertex

/-- Every vertex of a simplicial set determines its canonical vertex after subdivision. -/
noncomputable def barycentricSubdivisionVertex
    (X : SSet.{0}) (x : X.obj (Opposite.op (SimplexCategory.mk 0))) :
    (SSet.sd.obj X).obj (Opposite.op (SimplexCategory.mk 0)) :=
  (SSet.sd.map (SSet.yonedaEquiv.symm x)).app _ subdividedStandardZeroVertex

/-- The last-vertex map sends the canonical subdivided vertex of `Δ[0]` to its unique
vertex. -/
theorem subdivisionLastVertex_subdividedStandardZeroVertex :
    (SubdivisionBasic.subdivisionLastVertex.app (Δ[0] : SSet.{0})).app _
        subdividedStandardZeroVertex =
      SSet.stdSimplex.objEquiv.symm (𝟙 (SimplexCategory.mk 0)) := by
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i
  exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm

/-- The last-vertex map is a left inverse to barycentric subdivision on vertices. -/
theorem subdivisionLastVertex_barycentricSubdivisionVertex
    (X : SSet.{0}) (x : X.obj (Opposite.op (SimplexCategory.mk 0))) :
    (SubdivisionBasic.subdivisionLastVertex.app X).app _ (barycentricSubdivisionVertex X x) = x := by
  let f : (Δ[0] : SSet.{0}) ⟶ X := SSet.yonedaEquiv.symm x
  have hx := ConcreteCategory.congr_hom (NatTrans.congr_app
    (SubdivisionBasic.subdivisionLastVertex.naturality f)
    (Opposite.op (SimplexCategory.mk 0))) subdividedStandardZeroVertex
  change (SubdivisionBasic.subdivisionLastVertex.app X).app _
      ((SSet.sd.map f).app _ subdividedStandardZeroVertex) =
    f.app _ ((SubdivisionBasic.subdivisionLastVertex.app (Δ[0] : SSet.{0})).app _
      subdividedStandardZeroVertex) at hx
  rw [subdivisionLastVertex_subdividedStandardZeroVertex] at hx
  change (SubdivisionBasic.subdivisionLastVertex.app X).app _
      ((SSet.sd.map f).app _ subdividedStandardZeroVertex) = x
  rw [hx]
  change X.map (𝟙 (Opposite.op (SimplexCategory.mk 0))) x = x
  simp

/-- The degree-zero component of barycentric subdivision on integral simplicial chains. -/
noncomputable def barycentricSubdivisionChainMapZero (X : SSet.{0}) :
    (X.chainComplex (AddCommGrpCat.of ℤ)).X 0 ⟶
      ((SSet.sd.obj X).chainComplex (AddCommGrpCat.of ℤ)).X 0 :=
  Sigma.desc (fun x ↦ (SSet.sd.obj X).ιChainComplex
    (barycentricSubdivisionVertex X x))

@[reassoc (attr := simp)]
theorem iota_barycentricSubdivisionChainMapZero
    (X : SSet.{0}) (x : X.obj (Opposite.op (SimplexCategory.mk 0))) :
    X.ιChainComplex x ≫ barycentricSubdivisionChainMapZero X =
      (SSet.sd.obj X).ιChainComplex (barycentricSubdivisionVertex X x) := by
  apply Sigma.ι_comp_desc

/-- In degree zero, barycentric subdivision followed by last vertex is exactly the identity. -/
theorem barycentricSubdivisionChainMapZero_comp_lastVertex
    (X : SSet.{0}) :
    barycentricSubdivisionChainMapZero X ≫
        (SubdivisionBasic.subdivisionLastVertexChainMap X).f 0 =
      𝟙 ((X.chainComplex (AddCommGrpCat.of ℤ)).X 0) := by
  apply X.chainComplex_hom_ext
  intro x
  rw [← Category.assoc, iota_barycentricSubdivisionChainMapZero]
  change (SSet.sd.obj X).ιChainComplex (barycentricSubdivisionVertex X x) ≫
      (SSet.chainComplexMap (SubdivisionBasic.subdivisionLastVertex.app X)
        (AddCommGrpCat.of ℤ)).f 0 = _
  rw [SSet.ι_chainComplexMap_f,
    subdivisionLastVertex_barycentricSubdivisionVertex]
  simp

end

end OAI.AlgebraicTopology.Singular.SubdivisionBarycentricChains
