import OAI.AlgebraicGeometry.DivisorClass.Chern.FramesFrame
import OAI.AlgebraicGeometry.DivisorClass.Chern.BundleLogarithms

/-! # Mixed Analytic Frames -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-!
# ChernClass: analytic evaluation of frame changes between isomorphic module sheaves
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)

/-- Evaluation of an actual transition can be computed on any common algebraic subopen. -/
theorem Line.Bundles.AlgebraicLineBundle.pointTransition_restrict (i j : X.carrier) (W : X.carrier.Opens)
    (hi : W ≤ L.trivializingOpen i) (hj : W ≤ L.trivializingOpen j)
    (p : Line.Bundles.AlgebraicLineBundle.analyticOpen X W) :
    L.pointTransition i j p.val (hi p.property) (hj p.property) =
      Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W (L.ambientTransitionOn i j W hi hj : Γ(X.carrier, W)) p := by
  let a : Fin 2 → X.carrier := ![i, j]
  let A := L.algebraicIntersection a
  have hWA : W ≤ A := by
    intro z hz
    apply (AlgebraicTopology.DeRham.Comparison.SmoothCech.mem_cechIntersection L.trivializingOpen a z).mpr
    intro k
    fin_cases k
    · exact hi hz
    · exact hj hz
  let u := L.ambientTransitionOn i j A
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen a 1)
  have hu : X.carrier.presheaf.map (homOfLE hWA).op (u : Γ(X.carrier, A)) =
      (L.ambientTransitionOn i j W hi hj : Γ(X.carrier, W)) :=
    congrArg Units.val (L.ambientTransitionOn_restrict i j hWA
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le L.trivializingOpen a 1))
  have he := Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict X hWA (u : Γ(X.carrier, A)) p
  rw [hu] at he
  exact he.symm

variable (M : Line.Bundles.AlgebraicLineBundle X) (e : L.sheaf ≅ M.sheaf)

/-- Evaluation of the mixed transition on the actual analytic intersection. -/
def Line.Bundles.AlgebraicLineBundle.mixedTransitionPair (i j : X.carrier) :
    C((L.analyticCover i ⊓ M.analyticCover j : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)), ℂ) :=
  (Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X (L.trivializingOpen i ⊓ M.trivializingOpen j)
    (L.mixedTransitionOn M e i j _ inf_le_left inf_le_right :
      Γ(X.carrier, L.trivializingOpen i ⊓ M.trivializingOpen j))).comp
    ⟨fun p => ⟨p.val, p.property⟩, continuous_subtype_val.subtype_mk (fun p => p.property)⟩

theorem Line.Bundles.AlgebraicLineBundle.mixedTransitionPair_ne_zero (i j : X.carrier)
    (p : (L.analyticCover i ⊓ M.analyticCover j : Opens (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver))) :
    L.mixedTransitionPair M e i j p ≠ 0 := Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_unit_ne_zero X _ _ _

abbrev Line.Bundles.AlgebraicLineBundle.mixedPointTransition (i j : X.carrier) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
    (hi : p ∈ L.analyticCover i) (hj : p ∈ M.analyticCover j) : ℂ :=
  L.mixedTransitionPair M e i j ⟨p, hi, hj⟩

theorem Line.Bundles.AlgebraicLineBundle.mixedPointTransition_restrict (i j : X.carrier) (W : X.carrier.Opens)
    (hi : W ≤ L.trivializingOpen i) (hj : W ≤ M.trivializingOpen j)
    (p : Line.Bundles.AlgebraicLineBundle.analyticOpen X W) :
    L.mixedPointTransition M e i j p.val (hi p.property) (hj p.property) =
      Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W (L.mixedTransitionOn M e i j W hi hj : Γ(X.carrier, W)) p := by
  let A := L.trivializingOpen i ⊓ M.trivializingOpen j
  have hWA : W ≤ A := le_inf hi hj
  let u := L.mixedTransitionOn M e i j A inf_le_left inf_le_right
  have hu : X.carrier.presheaf.map (homOfLE hWA).op (u : Γ(X.carrier, A)) =
      (L.mixedTransitionOn M e i j W hi hj : Γ(X.carrier, W)) :=
    congrArg Units.val (L.mixedTransitionOn_restrict M e i j hWA inf_le_left inf_le_right)
  have he := Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict X hWA (u : Γ(X.carrier, A)) p
  rw [hu] at he
  exact he.symm

/-- The actual sheaf isomorphism gives a continuous gauge equivalence on overlaps. -/
theorem Line.Bundles.AlgebraicLineBundle.mixedPointTransition_gauge (i j k l : X.carrier) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
    (hi : p ∈ L.analyticCover i) (hj : p ∈ L.analyticCover j)
    (hk : p ∈ M.analyticCover k) (hl : p ∈ M.analyticCover l) :
    M.pointTransition k l p hk hl =
      L.pointTransition i j p hi hj * L.mixedPointTransition M e j l p hj hl /
        L.mixedPointTransition M e i k p hi hk := by
  let W := (L.trivializingOpen i ⊓ L.trivializingOpen j) ⊓
    (M.trivializingOpen k ⊓ M.trivializingOpen l)
  have hWi : W ≤ L.trivializingOpen i := inf_le_left.trans inf_le_left
  have hWj : W ≤ L.trivializingOpen j := inf_le_left.trans inf_le_right
  have hWk : W ≤ M.trivializingOpen k := inf_le_right.trans inf_le_left
  have hWl : W ≤ M.trivializingOpen l := inf_le_right.trans inf_le_right
  let q : Line.Bundles.AlgebraicLineBundle.analyticOpen X W := ⟨p, ⟨hi, hj⟩, ⟨hk, hl⟩⟩
  have hv := congrArg (fun u : Γ(X.carrier, W)ˣ =>
    Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W (u : Γ(X.carrier, W)) q)
    (L.mixedTransitionOn_square M e i j k l W hWi hWj hWk hWl)
  change Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W ((L.mixedTransitionOn M e i k W hWi hWk : Γ(X.carrier, W)) *
      (M.ambientTransitionOn k l W hWk hWl : Γ(X.carrier, W))) q =
    Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X W ((L.ambientTransitionOn i j W hWi hWj : Γ(X.carrier, W)) *
      (L.mixedTransitionOn M e j l W hWj hWl : Γ(X.carrier, W))) q at hv
  rw [Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_mul, Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_mul,
    ← Line.Bundles.AlgebraicLineBundle.mixedPointTransition_restrict, ← Line.Bundles.AlgebraicLineBundle.pointTransition_restrict,
    ← Line.Bundles.AlgebraicLineBundle.pointTransition_restrict, ← Line.Bundles.AlgebraicLineBundle.mixedPointTransition_restrict] at hv
  apply (eq_div_iff (L.mixedTransitionPair_ne_zero M e i k ⟨p, hi, hk⟩)).mpr
  exact (mul_comm _ _).trans hv

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
