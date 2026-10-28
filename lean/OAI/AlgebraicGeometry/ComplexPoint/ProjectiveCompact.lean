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
import OAI.AlgebraicGeometry.ComplexPoint.ClosedImmersion
import OAI.AlgebraicGeometry.ComplexPoint.Projective
import OAI.CategoryTheory.ConcreteCategory.Notation

/-! # Projective Compact -/

namespace OAI.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-!
# Analytic compactness of a projective complex scheme

A projective presentation of a complex scheme is a closed immersion into scheme-theoretic
projective space. On complex points it therefore induces a closed topological embedding into the
complex points of projective space, which are analytically compact.

Consequently the analytic complex points of any projective complex scheme form a compact space.
-/

open _root_.CategoryTheory Opposite _root_.TopologicalSpace _root_.Topology

namespace ComplexPoint.ProjectiveCompact.ProjectiveSpace.Presentation

/-- The immersion of a projective presentation, bundled over the complex base. -/
noncomputable abbrev overImmersion {X : Scheme} {f : X ⟶ Spec ↧ℂ}
    (P : Foundations.ProjectiveSpaceIs.ProjectiveSpace.Presentation f) :
    Over.mk f ⟶
      Over.mk (Foundations.ProjectiveSpaceIs.ProjectiveSpace.toBase (Fin (P.ambientDimension + 1)) (Spec ↧ℂ)) :=
  Over.homMk P.immersion P.immersion_toBase

/-- The continuous map on complex points induced by an explicit projective presentation. -/
noncomputable def analyticImmersion {X : Scheme} {f : X ⟶ Spec ↧ℂ}
    (P : Foundations.ProjectiveSpaceIs.ProjectiveSpace.Presentation f) :
    @ContinuousMap (Basic.ComplexSchemePoint (Over.mk f))
      (Basic.ComplexSchemePoint (Over.mk (Foundations.ProjectiveSpaceIs.ProjectiveSpace.toBase (Fin (P.ambientDimension + 1)) (Spec ↧ℂ))))
      Basic.Point.analyticTopology Basic.Point.analyticTopology :=
  Basic.Point.continuousMap (overImmersion P)

/-- The analytic map of an explicit projective presentation is a closed topological
embedding. -/
lemma analyticImmersion_isClosedEmbedding {X : Scheme} {f : X ⟶ Spec ↧ℂ}
    (P : Foundations.ProjectiveSpaceIs.ProjectiveSpace.Presentation f) :
    @IsClosedEmbedding (Basic.ComplexSchemePoint (Over.mk f))
      (Basic.ComplexSchemePoint (Over.mk (Foundations.ProjectiveSpaceIs.ProjectiveSpace.toBase (Fin (P.ambientDimension + 1)) (Spec ↧ℂ))))
      Basic.Point.analyticTopology Basic.Point.analyticTopology (analyticImmersion P) := by
  let : IsClosedImmersion (overImmersion P).left := P.isClosedImmersion
  exact Basic.ComplexSchemePoint.isClosedEmbedding_map_of_closedImmersion (overImmersion P)

/-- The analytic complex points of an explicit projective presentation form a compact space. -/
theorem complexPoint_compactSpace {X : Scheme} {f : X ⟶ Spec ↧ℂ}
    (P : Foundations.ProjectiveSpaceIs.ProjectiveSpace.Presentation f) :
    @CompactSpace (Basic.ComplexSchemePoint (Over.mk f)) Basic.Point.analyticTopology := by
  exact (analyticImmersion_isClosedEmbedding P).compactSpace

end ComplexPoint.ProjectiveCompact.ProjectiveSpace.Presentation

/-- The analytic complex points of a projective complex scheme form a compact space. -/
noncomputable instance Foundations.ProjectiveSpaceIs.IsProjective.complexPoint_compactSpace {X : Over (Spec ↧ℂ)}
    [h : Foundations.ProjectiveSpaceIs.IsProjective X.hom] : CompactSpace (ComplexPoint.Basic.ComplexSchemePoint X) :=
  ComplexPoint.ProjectiveCompact.ProjectiveSpace.Presentation.complexPoint_compactSpace
    (Classical.choice h.nonempty_presentation)

end OAI.AlgebraicGeometry
