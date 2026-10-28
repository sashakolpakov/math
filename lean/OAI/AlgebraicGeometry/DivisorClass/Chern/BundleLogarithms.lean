import OAI.AlgebraicGeometry.DivisorClass.Chern.Cocycle
import OAI.AlgebraicGeometry.DivisorClass.Chern.LogRefinementOpen
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveVarietyCompactness

/-! # Bundle Logarithms -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-!
# ChernClass: logarithmic transition data of actual algebraic line bundles

Compactness and normality of the genuine analytic point space provide a
logarithmic refinement of the actual algebraic trivializing cover.
-/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace BundleLogarithms.Construction

variable {T I : Type} [TopologicalSpace T]

/-- A pairwise intersection agrees with the intersection of its two-entry tuple. -/
theorem pair_le_cechIntersection (U : I → Opens T) (a : Fin 2 → I) :
    U (a 0) ⊓ U (a 1) ≤ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a := by
  intro x hx
  apply (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection U a x).mpr
  intro k
  fin_cases k
  · exact hx.1
  · exact hx.2

/-- The reverse inclusion is given by the two coordinate inclusions. -/
theorem cechIntersection_le_pair (U : I → Opens T) (a : Fin 2 → I) :
    AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection U a ≤ U (a 0) ⊓ U (a 1) :=
  le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le U a 1)

end BundleLogarithms.Construction

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)

/-- The actual transition function expressed on a binary intersection. -/
def Line.Bundles.AlgebraicLineBundle.transitionPair (i j : X.carrier) :
    C((L.analyticCover i ⊓ L.analyticCover j : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)), ℂ) :=
  (L.transitionCech ![i, j]).comp
    (LogRefinementOpen.Construction.openInclusionMap (BundleLogarithms.Construction.pair_le_cechIntersection L.analyticCover ![i, j]))

theorem Line.Bundles.AlgebraicLineBundle.transitionPair_ne_zero (i j : X.carrier)
    (p : (L.analyticCover i ⊓ L.analyticCover j : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))) :
    L.transitionPair i j p ≠ 0 := L.transitionCech_ne_zero _ _

theorem Line.Bundles.AlgebraicLineBundle.transitionCech_congr {a b : Fin 2 → X.carrier} (hab : a = b)
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover a) (q : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover b)
    (hpq : p.val = q.val) : L.transitionCech a p = L.transitionCech b q := by
  subst b
  have h : p = q := Subtype.ext hpq
  subst q
  rfl

/-- Choose the proved logarithmic refinement of the actual line-bundle transitions. -/
def Line.Bundles.AlgebraicLineBundle.bundleLogRefinement : LogRefinementOpen.Construction.CompactLogarithmicRefinement L.analyticCover L.transitionPair :=
  Classical.choice (LogRefinementOpen.Construction.nonempty_compactLogarithmicRefinement L.analyticCover
    L.analyticCover_covers L.transitionPair L.transitionPair_ne_zero)

/-- Index of a logarithmic chart: a center and one of the finitely many algebraic charts. -/
abbrev Line.Bundles.AlgebraicLineBundle.LogCoverIndex :=
  ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver × L.bundleLogRefinement.charts

/-- The refined analytic cover carrying continuous logarithms. -/
abbrev Line.Bundles.AlgebraicLineBundle.logCover : L.LogCoverIndex → Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) :=
  L.bundleLogRefinement.refinement.cover

/-- The algebraic chart to which a logarithmic chart is subordinate. -/
abbrev Line.Bundles.AlgebraicLineBundle.logParent (a : L.LogCoverIndex) : X.carrier := a.2.val

theorem Line.Bundles.AlgebraicLineBundle.logCover_subset (a : L.LogCoverIndex) :
    L.logCover a ≤ L.analyticCover (L.logParent a) :=
  L.bundleLogRefinement.refinement.subset a

theorem Line.Bundles.AlgebraicLineBundle.logCover_covers (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver) :
    ∃ a, p ∈ L.logCover a := L.bundleLogRefinement.refinement.covers p

/-- Logarithms of the actual transitions on the refined cover, as a Cech cochain. -/
def Line.Bundles.AlgebraicLineBundle.bundleLogCech : LogCech.RationalCech.LogCechCochain
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) L.logCover :=
  fun a => (L.bundleLogRefinement.refinement.logarithm (a 0) (a 1)).comp
    (LogRefinementOpen.Construction.openInclusionMap (BundleLogarithms.Construction.cechIntersection_le_pair L.logCover a))

theorem Line.Bundles.AlgebraicLineBundle.logIntersection_subset {n : ℕ} (a : Fin (n + 1) → L.LogCoverIndex) :
    AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a ≤ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover (L.logParent ∘ a) := by
  intro p hp
  apply (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection L.analyticCover (L.logParent ∘ a) p).mpr
  intro k
  exact L.logCover_subset (a k) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.logCover a k hp)

/-- Exponentiating the constructed logarithm recovers the original bundle transition. -/
theorem Line.Bundles.AlgebraicLineBundle.exp_bundleLogCech (a : Fin 2 → L.LogCoverIndex)
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.logCover a) :
    Complex.exp (L.bundleLogCech a p) =
      L.transitionCech (L.logParent ∘ a) ⟨p.val, L.logIntersection_subset a p.property⟩ := by
  have h := L.bundleLogRefinement.refinement.exp_logarithm (a 0) (a 1)
    (LogRefinementOpen.Construction.openInclusionMap (BundleLogarithms.Construction.cechIntersection_le_pair L.logCover a) p)
  have ha : ![L.logParent (a 0), L.logParent (a 1)] = L.logParent ∘ a := by
    funext k
    fin_cases k <;> rfl
  change Complex.exp (L.bundleLogCech a p) =
    L.transitionCech ![L.logParent (a 0), L.logParent (a 1)] _ at h
  exact h.trans (L.transitionCech_congr ha _ _ rfl)

/-- The constructed logarithms satisfy the exponential cocycle identity. -/
theorem Line.Bundles.AlgebraicLineBundle.bundleLogCech_cocycle : LogCech.RationalCech.ExponentialCocycle
    (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)) L.logCover L.bundleLogCech := by
  intro a p
  change Complex.exp (L.bundleLogCech (a ∘ (2 : Fin 3).succAbove) _) *
    Complex.exp (L.bundleLogCech (a ∘ (0 : Fin 3).succAbove) _) =
    Complex.exp (L.bundleLogCech (a ∘ (1 : Fin 3).succAbove) _)
  rw [Line.Bundles.AlgebraicLineBundle.exp_bundleLogCech, Line.Bundles.AlgebraicLineBundle.exp_bundleLogCech, Line.Bundles.AlgebraicLineBundle.exp_bundleLogCech]
  exact L.transitionCech_cocycle (L.logParent ∘ a)
    ⟨p.val, L.logIntersection_subset a p.property⟩

end

/-!
# ChernClass: the actual algebraic transition functions obey change-of-frame identities

All values below are evaluations of the genuine frame-transition units on a
common algebraic open set. The identities follow from composition of frames.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)

/-- A transition evaluated on a common finite intersection of algebraic charts. -/
def Line.Bundles.AlgebraicLineBundle.transitionValue {n : ℕ} (a : Fin (n + 1) → X.carrier) (i j : Fin (n + 1))
    (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover a) : ℂ :=
  L.evaluateOnIntersection a
    (L.ambientTransitionOn (a i) (a j) (L.algebraicIntersection a)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen a i)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen a j) : Γ(X.carrier, L.algebraicIntersection a)) p

theorem Line.Bundles.AlgebraicLineBundle.transitionValue_ne_zero {n : ℕ} (a : Fin (n + 1) → X.carrier)
    (i j : Fin (n + 1)) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover a) :
    L.transitionValue a i j p ≠ 0 := Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_unit_ne_zero X _ _ _

/-- Restricting an original pairwise transition evaluates the same actual unit. -/
theorem Line.Bundles.AlgebraicLineBundle.transitionValue_eq {n : ℕ} (a : Fin (n + 1) → X.carrier)
    (f : Fin 2 → Fin (n + 1)) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover a) :
    L.transitionCech (a ∘ f) ⟨p.val, AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le_precomp L.analyticCover a f p.property⟩ =
      L.transitionValue a (f 0) (f 1) p := L.transitionCech_restrict a f p

theorem Line.Bundles.AlgebraicLineBundle.transitionValue_cocycle {n : ℕ} (a : Fin (n + 1) → X.carrier)
    (i j k : Fin (n + 1)) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover a) :
    L.transitionValue a i j p * L.transitionValue a j k p = L.transitionValue a i k p := by
  unfold Line.Bundles.AlgebraicLineBundle.transitionValue
  rw [← Line.Bundles.AlgebraicLineBundle.evaluateOnIntersection_mul]
  exact congrArg (fun u : Γ(X.carrier, L.algebraicIntersection a)ˣ =>
    L.evaluateOnIntersection a (u : Γ(X.carrier, L.algebraicIntersection a)) p)
    (L.ambientTransitionOn_cocycle (a i) (a j) (a k) (L.algebraicIntersection a)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen a i)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen a j)
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen a k))

/-- Changing the frames at both endpoints multiplies a transition by their ratio. -/
theorem Line.Bundles.AlgebraicLineBundle.transitionValue_gauge {n : ℕ} (a : Fin (n + 1) → X.carrier)
    (i j k l : Fin (n + 1)) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover a) :
    L.transitionValue a k l p = L.transitionValue a i j p *
      L.transitionValue a j l p / L.transitionValue a i k p := by
  apply (eq_div_iff (L.transitionValue_ne_zero a i k p)).mpr
  rw [mul_comm, Line.Bundles.AlgebraicLineBundle.transitionValue_cocycle, Line.Bundles.AlgebraicLineBundle.transitionValue_cocycle]

/-- The transition at a point belonging to both algebraic trivializing charts. -/
abbrev Line.Bundles.AlgebraicLineBundle.pointTransition (i j : X.carrier) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
    (hi : p ∈ L.analyticCover i) (hj : p ∈ L.analyticCover j) : ℂ :=
  L.transitionPair i j ⟨p, hi, hj⟩

theorem Line.Bundles.AlgebraicLineBundle.pointTransition_eq_value {n : ℕ} (a : Fin (n + 1) → X.carrier)
    (i j : Fin (n + 1)) (p : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover a) :
    L.pointTransition (a i) (a j) p.val
        (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.analyticCover a i p.property)
        (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.analyticCover a j p.property) =
      L.transitionValue a i j p := by
  have ha : ![a i, a j] = a ∘ ![i, j] := by
    funext k
    fin_cases k <;> rfl
  exact (L.transitionCech_congr ha _ _ rfl).trans (L.transitionValue_eq a ![i, j] p)

/-- Pointwise change-of-frame formula for four arbitrary algebraic charts. -/
theorem Line.Bundles.AlgebraicLineBundle.pointTransition_gauge (i j k l : X.carrier) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
    (hi : p ∈ L.analyticCover i) (hj : p ∈ L.analyticCover j)
    (hk : p ∈ L.analyticCover k) (hl : p ∈ L.analyticCover l) :
    L.pointTransition k l p hk hl =
      L.pointTransition i j p hi hj * L.pointTransition j l p hj hl /
        L.pointTransition i k p hi hk := by
  let a : Fin 4 → X.carrier := ![i, j, k, l]
  have hp : p ∈ AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover a := by
    apply (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection L.analyticCover a p).mpr
    intro t
    fin_cases t
    · exact hi
    · exact hj
    · exact hk
    · exact hl
  let q : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection L.analyticCover a := ⟨p, hp⟩
  calc
    L.pointTransition k l p hk hl = L.transitionValue a 2 3 q :=
      L.pointTransition_eq_value a 2 3 q
    _ = L.transitionValue a 0 1 q * L.transitionValue a 1 3 q /
        L.transitionValue a 0 2 q := L.transitionValue_gauge a 0 1 2 3 q
    _ = L.pointTransition i j p hi hj * L.pointTransition j l p hj hl /
        L.pointTransition i k p hi hk := by
      rw [← Line.Bundles.AlgebraicLineBundle.pointTransition_eq_value, ← Line.Bundles.AlgebraicLineBundle.pointTransition_eq_value, ← Line.Bundles.AlgebraicLineBundle.pointTransition_eq_value]
      rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
