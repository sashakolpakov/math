import OAI.RepresentationTheory.Theta.Geometric.SchemeLineFrame
import OAI.RepresentationTheory.Theta.Geometric.SchemeSectionNaturality
import OAI.AlgebraicGeometry.DivisorClass.Chern.LogCech

/-! # Scheme Line Cocycle -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The actual section frames of a line bundle on an arbitrary complex
scheme give a continuous nonvanishing analytic transition cocycle. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.RepresentationTheory.Theta.Geometric.SchemeSectionNaturality.SchemeSectionEvaluation

variable {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} {L : AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X.left} (A : SchemeLineFrame.SchemeLineAtlas L)

/-- The actual analytic open cover supplied by the chosen sheaf trivializations. -/
abbrev SchemeLineFrame.SchemeLineAtlas.analyticCover (i : X.left) : Opens (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :=
  SchemeSectionNaturality.SchemeSectionEvaluation.analyticOpen X (A.domain i)

theorem SchemeLineFrame.SchemeLineAtlas.analyticCover_covers (p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X) :
    ∃ i, p ∈ A.analyticCover i :=
  ⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p, A.contains _⟩

/-- The corresponding finite intersection of algebraic chart domains. -/
abbrev SchemeLineFrame.SchemeLineAtlas.algebraicIntersection {n : ℕ} (a : Fin (n + 1) → X.left) :=
  AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection A.domain a

/-- The point-identification for finite intersections is literally the identity on points. -/
def SchemeLineFrame.SchemeLineAtlas.intersectionPointMap {n : ℕ} (a : Fin (n + 1) → X.left) :
    C(AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection A.analyticCover a, SchemeSectionNaturality.SchemeSectionEvaluation.analyticOpen X (A.algebraicIntersection a)) := by
  let e : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection A.analyticCover a ≃ₜ
      SchemeSectionNaturality.SchemeSectionEvaluation.analyticOpen X (A.algebraicIntersection a) := Homeomorph.setCongr (by
    ext p
    simp only [SetLike.mem_coe, AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection, SchemeSectionNaturality.SchemeSectionEvaluation.analyticOpen, Set.mem_preimage,
      Opens.coe_mk, SchemeLineFrame.SchemeLineAtlas.algebraicIntersection, SchemeLineFrame.SchemeLineAtlas.analyticCover]
    rfl)
  exact ⟨e, e.continuous⟩

/-- Evaluate a regular section on the actual analytic finite intersection. -/
def SchemeLineFrame.SchemeLineAtlas.evaluateOnIntersection {n : ℕ} (a : Fin (n + 1) → X.left)
    (s : Γ(X.left, A.algebraicIntersection a)) :
    C(AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection A.analyticCover a, ℂ) :=
  (SchemeSectionNaturality.SchemeSectionEvaluation.sectionEvaluationOn X (A.algebraicIntersection a) s).comp (A.intersectionPointMap a)

theorem SchemeLineFrame.SchemeLineAtlas.evaluateOnIntersection_mul {n : ℕ} (a : Fin (n + 1) → X.left)
    (s t : Γ(X.left, A.algebraicIntersection a))
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection A.analyticCover a) :
    A.evaluateOnIntersection a (s * t) p =
      A.evaluateOnIntersection a s p * A.evaluateOnIntersection a t p :=
  SchemeSectionNaturality.SchemeSectionEvaluation.sectionEvaluationOn_mul X _ s t _

/-- Evaluation commutes with forgetting indices and restricting the regular section. -/
theorem SchemeLineFrame.SchemeLineAtlas.evaluateOnIntersection_precomp {n m : ℕ}
    (a : Fin (m + 1) → X.left) (f : Fin (n + 1) → Fin (m + 1))
    (s : Γ(X.left, A.algebraicIntersection (a ∘ f)))
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection A.analyticCover a) :
    A.evaluateOnIntersection (a ∘ f) s
        ⟨p.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp A.analyticCover a f p.property⟩ =
      A.evaluateOnIntersection a
        (X.left.presheaf.map (homOfLE
          (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp A.domain a f)).op s) p := by
  exact (SchemeSectionNaturality.SchemeSectionEvaluation.sectionEvaluationOn_restrict X
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp A.domain a f) s
    (A.intersectionPointMap a p)).symm

/-- The genuine nonvanishing analytic transition function on each pairwise intersection. -/
def SchemeLineFrame.SchemeLineAtlas.transitionCech : AlgebraicGeometry.DivisorClass.Chern.Rational.Cech.RationalCech.CechCochain
    (AlgebraicGeometry.DivisorClass.Chern.LogCech.RationalCech.continuousComplexPresheaf (TopCat.of (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))
    A.analyticCover 1 :=
  fun a => A.evaluateOnIntersection a
    (A.transition (a 0) (a 1) (A.algebraicIntersection a)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le A.domain a 0)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le A.domain a 1) :
        Γ(X.left, A.algebraicIntersection a))

theorem SchemeLineFrame.SchemeLineAtlas.transitionCech_ne_zero (a : Fin 2 → X.left)
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection A.analyticCover a) : A.transitionCech a p ≠ 0 :=
  SchemeSectionNaturality.SchemeSectionEvaluation.sectionEvaluationOn_unit_ne_zero X _ _ _

/-- Pulling a transition to a common intersection gives the transition of its restricted frames. -/
theorem SchemeLineFrame.SchemeLineAtlas.transitionCech_restrict {n : ℕ} (a : Fin (n + 1) → X.left)
    (f : Fin 2 → Fin (n + 1)) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection A.analyticCover a) :
    A.transitionCech (a ∘ f)
        ⟨p.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp A.analyticCover a f p.property⟩ =
      A.evaluateOnIntersection a
        (A.transition (a (f 0)) (a (f 1)) (A.algebraicIntersection a)
          (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le A.domain a (f 0))
          (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le A.domain a (f 1)) :
            Γ(X.left, A.algebraicIntersection a)) p := by
  unfold SchemeLineFrame.SchemeLineAtlas.transitionCech
  rw [SchemeLineFrame.SchemeLineAtlas.evaluateOnIntersection_precomp]
  have h := A.transition_restrict (a (f 0)) (a (f 1))
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp A.domain a f)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le A.domain (a ∘ f) 0)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le A.domain (a ∘ f) 1)
  exact congrArg (fun u : Γ(X.left, A.algebraicIntersection a)ˣ =>
    A.evaluateOnIntersection a (u : Γ(X.left, A.algebraicIntersection a)) p) h

/-- The actual analytic transition functions satisfy the multiplicative Cech cocycle identity. -/
theorem SchemeLineFrame.SchemeLineAtlas.transitionCech_cocycle (a : Fin 3 → X.left)
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection A.analyticCover a) :
    A.transitionCech (a ∘ (2 : Fin 3).succAbove)
        ⟨p.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp A.analyticCover a _ p.property⟩ *
      A.transitionCech (a ∘ (0 : Fin 3).succAbove)
        ⟨p.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp A.analyticCover a _ p.property⟩ =
    A.transitionCech (a ∘ (1 : Fin 3).succAbove)
        ⟨p.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp A.analyticCover a _ p.property⟩ := by
  rw [SchemeLineFrame.SchemeLineAtlas.transitionCech_restrict, SchemeLineFrame.SchemeLineAtlas.transitionCech_restrict, SchemeLineFrame.SchemeLineAtlas.transitionCech_restrict,
    ← SchemeLineFrame.SchemeLineAtlas.evaluateOnIntersection_mul]
  exact congrArg (fun u : Γ(X.left, A.algebraicIntersection a)ˣ =>
    A.evaluateOnIntersection a (u : Γ(X.left, A.algebraicIntersection a)) p)
    (A.transition_cocycle (a 0) (a 1) (a 2) (A.algebraicIntersection a)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le A.domain a 0)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le A.domain a 1)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le A.domain a 2))

end

end OAI.RepresentationTheory.Theta.Geometric
