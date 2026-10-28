import OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticCover
import OAI.AlgebraicGeometry.DivisorClass.Chern.LogCech

/-! # Cocycle -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-!
# ChernClass: the actual analytic transition cocycle of an algebraic line bundle

The open cover and its transition functions are extracted from the algebraic
line bundle's sheaf trivializations. All identities follow from section-frame
naturality, evaluation, and composition of the actual frames.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)

/-- The actual analytic open cover supplied by the chosen sheaf trivializations. -/
abbrev Line.Bundles.AlgebraicLineBundle.analyticCover (i : X.carrier) : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) :=
  Line.Bundles.AlgebraicLineBundle.analyticOpen X (L.trivializingOpen i)

theorem Line.Bundles.AlgebraicLineBundle.analyticCover_covers (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) :
    ∃ i, p ∈ L.analyticCover i :=
  ⟨ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p, L.mem_trivializingOpen _⟩

/-- The corresponding finite intersection of algebraic chart domains. -/
abbrev Line.Bundles.AlgebraicLineBundle.algebraicIntersection {n : ℕ} (a : Fin (n + 1) → X.carrier) :=
  AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.trivializingOpen a

/-- The point-identification for finite intersections is literally the identity on points. -/
def Line.Bundles.AlgebraicLineBundle.intersectionPointMap {n : ℕ} (a : Fin (n + 1) → X.carrier) :
    C(AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover a, Line.Bundles.AlgebraicLineBundle.analyticOpen X (L.algebraicIntersection a)) := by
  let e : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover a ≃ₜ
      Line.Bundles.AlgebraicLineBundle.analyticOpen X (L.algebraicIntersection a) := Homeomorph.setCongr (by
    ext p
    simp only [SetLike.mem_coe, AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection, Line.Bundles.AlgebraicLineBundle.analyticOpen, Set.mem_preimage,
      Opens.coe_mk, Line.Bundles.AlgebraicLineBundle.algebraicIntersection, Line.Bundles.AlgebraicLineBundle.analyticCover]
    rfl)
  exact ⟨e, e.continuous⟩

/-- Evaluate a regular section on the actual analytic finite intersection. -/
def Line.Bundles.AlgebraicLineBundle.evaluateOnIntersection {n : ℕ} (a : Fin (n + 1) → X.carrier)
    (s : Γ(X.carrier, L.algebraicIntersection a)) :
    C(AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover a, ℂ) :=
  (Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X (L.algebraicIntersection a) s).comp (L.intersectionPointMap a)

theorem Line.Bundles.AlgebraicLineBundle.evaluateOnIntersection_mul {n : ℕ} (a : Fin (n + 1) → X.carrier)
    (s t : Γ(X.carrier, L.algebraicIntersection a))
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover a) :
    L.evaluateOnIntersection a (s * t) p =
      L.evaluateOnIntersection a s p * L.evaluateOnIntersection a t p :=
  Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_mul X _ s t _

/-- Evaluation commutes with forgetting indices and restricting the regular section. -/
theorem Line.Bundles.AlgebraicLineBundle.evaluateOnIntersection_precomp {n m : ℕ}
    (a : Fin (m + 1) → X.carrier) (f : Fin (n + 1) → Fin (m + 1))
    (s : Γ(X.carrier, L.algebraicIntersection (a ∘ f)))
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover a) :
    L.evaluateOnIntersection (a ∘ f) s
        ⟨p.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp L.analyticCover a f p.property⟩ =
      L.evaluateOnIntersection a
        (X.carrier.presheaf.map (homOfLE
          (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp L.trivializingOpen a f)).op s) p := by
  exact (Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict X
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp L.trivializingOpen a f) s
    (L.intersectionPointMap a p)).symm

/-- The genuine nonvanishing analytic transition function on each pairwise intersection. -/
def Line.Bundles.AlgebraicLineBundle.transitionCech : Rational.Cech.RationalCech.CechCochain
    (LogCech.RationalCech.continuousComplexPresheaf (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)))
    L.analyticCover 1 :=
  fun a => L.evaluateOnIntersection a
    (L.ambientTransitionOn (a 0) (a 1) (L.algebraicIntersection a)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen a 0)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen a 1) :
        Γ(X.carrier, L.algebraicIntersection a))

theorem Line.Bundles.AlgebraicLineBundle.transitionCech_ne_zero (a : Fin 2 → X.carrier)
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover a) : L.transitionCech a p ≠ 0 :=
  Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_unit_ne_zero X _ _ _

/-- Pulling a transition to a common intersection gives the transition of its restricted frames. -/
theorem Line.Bundles.AlgebraicLineBundle.transitionCech_restrict {n : ℕ} (a : Fin (n + 1) → X.carrier)
    (f : Fin 2 → Fin (n + 1)) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover a) :
    L.transitionCech (a ∘ f)
        ⟨p.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp L.analyticCover a f p.property⟩ =
      L.evaluateOnIntersection a
        (L.ambientTransitionOn (a (f 0)) (a (f 1)) (L.algebraicIntersection a)
          (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen a (f 0))
          (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen a (f 1)) :
            Γ(X.carrier, L.algebraicIntersection a)) p := by
  unfold Line.Bundles.AlgebraicLineBundle.transitionCech
  rw [Line.Bundles.AlgebraicLineBundle.evaluateOnIntersection_precomp]
  have h := L.ambientTransitionOn_restrict (a (f 0)) (a (f 1))
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp L.trivializingOpen a f)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen (a ∘ f) 0)
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen (a ∘ f) 1)
  exact congrArg (fun u : Γ(X.carrier, L.algebraicIntersection a)ˣ =>
    L.evaluateOnIntersection a (u : Γ(X.carrier, L.algebraicIntersection a)) p) h

/-- The actual analytic transition functions satisfy the multiplicative Cech cocycle identity. -/
theorem Line.Bundles.AlgebraicLineBundle.transitionCech_cocycle (a : Fin 3 → X.carrier)
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover a) :
    L.transitionCech (a ∘ (2 : Fin 3).succAbove)
        ⟨p.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp L.analyticCover a _ p.property⟩ *
      L.transitionCech (a ∘ (0 : Fin 3).succAbove)
        ⟨p.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp L.analyticCover a _ p.property⟩ =
    L.transitionCech (a ∘ (1 : Fin 3).succAbove)
        ⟨p.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp L.analyticCover a _ p.property⟩ := by
  rw [Line.Bundles.AlgebraicLineBundle.transitionCech_restrict, Line.Bundles.AlgebraicLineBundle.transitionCech_restrict, Line.Bundles.AlgebraicLineBundle.transitionCech_restrict,
    ← Line.Bundles.AlgebraicLineBundle.evaluateOnIntersection_mul]
  exact congrArg (fun u : Γ(X.carrier, L.algebraicIntersection a)ˣ =>
    L.evaluateOnIntersection a (u : Γ(X.carrier, L.algebraicIntersection a)) p)
    (L.ambientTransitionOn_cocycle (a 0) (a 1) (a 2) (L.algebraicIntersection a)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen a 0)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen a 1)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen a 2))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
