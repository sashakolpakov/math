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
import OAI.AlgebraicGeometry.Cycle.SupportEq
import OAI.AlgebraicGeometry.Cycle.ComponentDimension
import OAI.AlgebraicGeometry.Smooth.DimensionFormula
import OAI.CategoryTheory.ConcreteCategory.Notation
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Component Normal -/

namespace OAI.AlgebraicGeometry.Cycle.ComponentNormal

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Smooth geometry of cycle components

The reduced closure of a point in a smooth projective complex variety is an integral projective
scheme. This file records that its smooth locus is dense, that its smooth closed points are
dense, and that a smooth closed complex point can be chosen together with ambient étale
coordinates.

For an ambient scheme smooth of relative dimension `d`, a component whose generic point has
coheight `p` has dimension at most `d - p`. The later module `Smooth.CatenaryDimension` upgrades
this bound to equality. A simultaneous coordinate normal form of exact codimension `p` is still
not asserted here.
-/

open _root_.CategoryTheory _root_.Topology _root_.TopologicalSpace

variable (X : Over (Spec ↧ℂ))

/-- The smooth locus of a reduced cycle component is Zariski dense. -/
lemma dense_cycleComponent_smoothLocus
    [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left) :
    Dense
      ((Support.cycleComponentι X.left x ≫ X.hom).smoothLocus :
        Set (Support.cycleComponent X.left x)) :=
  (Support.cycleComponentι X.left x ≫ X.hom).dense_smoothLocus_of_perfectField

/-- The smooth locus of an integral cycle component is irreducible. -/
noncomputable instance cycleComponent_smoothLocus_irreducibleSpace
    [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left) :
    IrreducibleSpace
      (Support.cycleComponentι X.left x ≫ X.hom).smoothLocus := by
  obtain ⟨y, hy⟩ := (dense_cycleComponent_smoothLocus X x).nonempty
  let : Nonempty
      (Support.cycleComponentι X.left x ≫ X.hom).smoothLocus :=
    ⟨⟨y, hy⟩⟩
  exact
    (Support.cycleComponentι X.left x ≫ X.hom).smoothLocus.ι.isOpenEmbedding.irreducibleSpace

/-- The scheme points that are both smooth and closed are dense in a reduced cycle component. -/
lemma dense_cycleComponent_smooth_closedPoints
    [IsIntegral X.left] [Smooth X.hom] [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left) :
    Dense
      (((Support.cycleComponentι X.left x ≫ X.hom).smoothLocus :
          Set (Support.cycleComponent X.left x)) ∩
        closedPoints (Support.cycleComponent X.left x)) := by
  let f := Support.cycleComponentι X.left x ≫ X.hom
  let : JacobsonSpace (Support.cycleComponent X.left x) :=
    LocallyOfFiniteType.jacobsonSpace f
  exact dense_iff_closure_eq.mpr ((JacobsonSpace.closure_inter_closedPoints_eq_closure
    f.smoothLocus.2.isLocallyClosed).trans
      (dense_iff_closure_eq.mp (dense_cycleComponent_smoothLocus X x)))

/-- The reduced component of a point of coheight `p` in a smooth complex `d`-fold has
topological Krull dimension at most `d - p`. -/
lemma topologicalKrullDim_cycleComponent_le_sub
    [IsIntegral X.left] [Smooth X.hom]
    [Foundations.ProjectiveSpaceIs.IsProjective X.hom] (x : X.left) {d p : ℕ}
    [SmoothOfRelativeDimension d X.hom] (hx : Order.coheight x = p) :
    topologicalKrullDim (Support.cycleComponent X.left x) ≤ d - p := by
  rw [ComponentDimension.topologicalKrullDim_cycleComponent]
  exact WithBot.coe_le_coe.mpr
    (OAI.AlgebraicGeometry.Smooth.DimensionFormula.SmoothOfRelativeDimension.height_le_sub_of_coheight_eq
      (f := X.hom) (d := d) x hx)

end

end OAI.AlgebraicGeometry.Cycle.ComponentNormal
