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
import OAI.AlgebraicGeometry.ComplexPoint.Basic
import OAI.CategoryTheory.ConcreteCategory.Notation
import OAI.Topology.Algebra.IsOpenUnits

/-! # Basic Ne -/

namespace OAI.AlgebraicGeometry.ComplexPoint

open _root_.AlgebraicGeometry

/-!
# Points over a commutative ring, and analytification

-/

/-! ### Constructions used only in proofs -/

section

open _root_.CategoryTheory _root_.Topology
open scoped CommRingCat.HomTopology

variable (R : Type) [CommRing R]

/-- A projective complex scheme is Noetherian. -/
theorem BasicNe.isNoetherian_of_isProjective (X : Over (Spec ↧ℂ))
    [Foundations.ProjectiveSpaceIs.IsProjective X.hom] : IsNoetherian X.left where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian X.hom
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace X.hom

variable {R}

variable {K : Type} [Field K] {X : Over (Spec ↧K)}

/-- Over a field, a `K`-point is a scheme point together with an embedding of its residue field.

This refines `stalkData`: the stalk homomorphism out of a local ring into a field factors through
the residue field. -/
noncomputable def Basic.Point.residueData (z : Basic.Point K X) :
    Σ x : X.left, X.left.residueField x ⟶ ↧K :=
  Scheme.SpecToEquivOfField K X.left z.left

end

open _root_.CategoryTheory _root_.Topology
open scoped CommRingCat.HomTopology

variable (R : Type) [CommRing R]

variable {R}

section IsLocalRing

variable [IsLocalRing R] {X : Over (Spec ↧R)}

variable [TopologicalSpace R]

variable [ContinuousMul R] [IsOpenUnits R]

/-- The `R`-points over a scheme open form an analytic open set. -/
lemma Basic.Point.isOpen_overOpen (U : X.left.Opens) :
    IsOpen (Basic.Point.overOpen U : Set (Basic.Point R X)) := by
  simpa using Basic.Point.isOpen_overOpen_inter_preimage U 0 Set.univ isOpen_univ

end IsLocalRing

variable {K : Type} [Field K] {X : Over (Spec ↧K)}

/-- Over a field, a `K`-point belongs to a principal open exactly when its defining function is
nonzero there. -/
lemma Basic.Point.mem_overOpen_basicOpen_iff_evaluate_ne_zero {U : X.left.Opens} (s : Γ(X.left, U))
    (z : Basic.Point K X) (hz : z ∈ Basic.Point.overOpen U) :
    z ∈ Basic.Point.overOpen (X.left.basicOpen s) ↔ Basic.Point.evaluate U s z ≠ 0 := by
  rw [Basic.Point.mem_overOpen_basicOpen_iff_isUnit_evaluate s z hz, isUnit_iff_ne_zero]

/-- Over a field, a regular function on a principal open of an affine open is a quotient
of regular functions on the whole affine open. -/
lemma Basic.Point.exists_evaluate_basicOpen_eq_div {U : X.left.Opens} (hU : IsAffineOpen U) (f : Γ(X.left, U))
    (t : Γ(X.left, X.left.basicOpen f)) :
    ∃ (k : ℕ) (a : Γ(X.left, U)), ∀ z : Basic.Point K X,
      z ∈ Basic.Point.overOpen (X.left.basicOpen f) →
        Basic.Point.evaluate (X.left.basicOpen f) t z = Basic.Point.evaluate U a z / Basic.Point.evaluate U f z ^ k := by
  obtain ⟨k, a, h⟩ :=
    Basic.Point.exists_evaluate_basicOpen_eq_inverse_mul (X := X) hU f t
  exact ⟨k, a, fun z hz ↦ by rw [h z hz, Ring.inverse_eq_inv', div_eq_inv_mul]⟩

end OAI.AlgebraicGeometry.ComplexPoint
