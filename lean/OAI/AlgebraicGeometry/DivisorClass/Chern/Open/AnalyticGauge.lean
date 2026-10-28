import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.MixedFrames
import OAI.AlgebraicGeometry.DivisorClass.Chern.AnalyticCover
import OAI.AlgebraicGeometry.DivisorClass.Chern.MixedAnalyticFrames

/-! # Analytic Gauge -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Open.AnalyticGauge

noncomputable section

/-!
# ChernClass: analytic gauge for the actual restriction of an algebraic line bundle

Mixed units from the original and restricted section frames give a
nonvanishing continuous change of frame. Its cocycle equation compares
the original evaluated transitions with the restricted bundle's own transitions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace AlgebraicLineBundle

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)
  (f : Y.toOver ⟶ X.toOver) [IsOpenImmersion f.left]

local notation "M" => L.restrictToOpen Y f.left

/-- The common algebraic domain of an original frame and a restricted frame. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openMixedDomain (i : X.carrier) (j : Y.carrier) : Y.carrier.Opens :=
  f.left ⁻¹ᵁ L.trivializingOpen i ⊓ (M).trivializingOpen j

theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openMixedDomain_image (i : X.carrier) (j : Y.carrier) :
    f.left ''ᵁ L.openMixedDomain f i j ≤ L.trivializingOpen i := by
  rintro _ ⟨y, hy, rfl⟩
  exact hy.1

/-- Evaluation of the genuine mixed regular unit. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openMixedTransitionPair (i : X.carrier) (j : Y.carrier) :
    C(Line.Bundles.AlgebraicLineBundle.analyticOpen Y (L.openMixedDomain f i j), ℂ) :=
  Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn Y (L.openMixedDomain f i j)
    (L.openMixedTransitionOn f.left i j _ (L.openMixedDomain_image f i j) inf_le_right :
      Γ(Y.carrier, L.openMixedDomain f i j))

theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openMixedTransitionPair_ne_zero (i : X.carrier) (j : Y.carrier)
    (p : Line.Bundles.AlgebraicLineBundle.analyticOpen Y (L.openMixedDomain f i j)) :
    L.openMixedTransitionPair f i j p ≠ 0 := Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_unit_ne_zero Y _ _ _

abbrev _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openMixedPointTransition (i : X.carrier) (j : Y.carrier)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y.toOver)
    (hi : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p ∈ L.analyticCover i) (hj : p ∈ (M).analyticCover j) : ℂ :=
  L.openMixedTransitionPair f i j ⟨p, hi, hj⟩

/-- The mixed point value can be computed on any smaller common algebraic domain. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openMixedPointTransition_restrict (i : X.carrier) (j : Y.carrier)
    (W : Y.carrier.Opens) (hi : f.left ''ᵁ W ≤ L.trivializingOpen i)
    (hj : W ≤ (M).trivializingOpen j) (p : Line.Bundles.AlgebraicLineBundle.analyticOpen Y W) :
    L.openMixedPointTransition f i j p.val (hi ⟨_, p.property, rfl⟩) (hj p.property) =
      Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn Y W (L.openMixedTransitionOn f.left i j W hi hj : Γ(Y.carrier, W)) p := by
  have hWA : W ≤ L.openMixedDomain f i j :=
    fun y hy => ⟨hi ⟨y, hy, rfl⟩, hj hy⟩
  have hu := congrArg Units.val (L.openMixedTransitionOn_restrict f.left i j hWA
    (L.openMixedDomain_image f i j) inf_le_right)
  change Y.carrier.presheaf.map (homOfLE hWA).op
      (L.openMixedTransitionOn f.left i j _ (L.openMixedDomain_image f i j) inf_le_right :
        Γ(Y.carrier, L.openMixedDomain f i j)) =
    (L.openMixedTransitionOn f.left i j W hi hj : Γ(Y.carrier, W)) at hu
  have he := Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict Y hWA
    (L.openMixedTransitionOn f.left i j _ (L.openMixedDomain_image f i j) inf_le_right :
      Γ(Y.carrier, L.openMixedDomain f i j)) p
  rw [hu] at he
  exact he.symm

/-- Original point transitions pull back by the genuine open-immersion scalar map. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.pointTransition_open_pullback (i j : X.carrier) (W : Y.carrier.Opens)
    (hi : f.left ''ᵁ W ≤ L.trivializingOpen i) (hj : f.left ''ᵁ W ≤ L.trivializingOpen j)
    (p : Line.Bundles.AlgebraicLineBundle.analyticOpen Y W) :
    L.pointTransition i j (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p.val)
        (hi ⟨_, p.property, rfl⟩) (hj ⟨_, p.property, rfl⟩) =
      Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn Y W
        ((f.left.appIso W).hom (L.ambientTransitionOn i j (f.left ''ᵁ W) hi hj :
          Γ(X.carrier, f.left ''ᵁ W))) p := by
  exact (L.pointTransition_restrict i j (f.left ''ᵁ W) hi hj
    (Line.Bundles.AlgebraicLineBundle.analyticOpenMap f (f.left ''ᵁ W) W (f.left.preimage_image_eq W).ge p)).trans
      (Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_appIso f W _ p).symm

/-- The actual line-bundle restriction supplies the analytic change-of-frame equation. -/
theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.Line.Bundles.AlgebraicLineBundle.openMixedPointTransition_gauge (i j : X.carrier) (k l : Y.carrier)
    (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y.toOver)
    (hi : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p ∈ L.analyticCover i)
    (hj : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p ∈ L.analyticCover j)
    (hk : p ∈ (M).analyticCover k) (hl : p ∈ (M).analyticCover l) :
    (M).pointTransition k l p hk hl =
      L.pointTransition i j (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) hi hj *
        L.openMixedPointTransition f j l p hj hl / L.openMixedPointTransition f i k p hi hk := by
  let W := (f.left ⁻¹ᵁ L.trivializingOpen i ⊓ f.left ⁻¹ᵁ L.trivializingOpen j) ⊓
    ((M).trivializingOpen k ⊓ (M).trivializingOpen l)
  have hWi : f.left ''ᵁ W ≤ L.trivializingOpen i := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy.1.1
  have hWj : f.left ''ᵁ W ≤ L.trivializingOpen j := by
    rintro _ ⟨y, hy, rfl⟩
    exact hy.1.2
  have hWk : W ≤ (M).trivializingOpen k := inf_le_right.trans inf_le_left
  have hWl : W ≤ (M).trivializingOpen l := inf_le_right.trans inf_le_right
  let q : Line.Bundles.AlgebraicLineBundle.analyticOpen Y W := ⟨p, ⟨hi, hj⟩, ⟨hk, hl⟩⟩
  let u : Γ(Y.carrier, W) := (f.left.appIso W).hom
    (L.ambientTransitionOn i j (f.left ''ᵁ W) hWi hWj : Γ(X.carrier, f.left ''ᵁ W))
  have hu : Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn Y W u q =
      L.pointTransition i j (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f p) hi hj :=
    (L.pointTransition_open_pullback f i j W hWi hWj q).symm
  have hv := congrArg (fun u : Γ(Y.carrier, W)ˣ => Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn Y W (u : Γ(Y.carrier, W)) q)
    (L.openMixedTransitionOn_square f.left i j k l W hWi hWj hWk hWl)
  change Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn Y W ((L.openMixedTransitionOn f.left i k W hWi hWk : Γ(Y.carrier, W)) *
      ((M).ambientTransitionOn k l W hWk hWl : Γ(Y.carrier, W))) q =
    Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn Y W (u *
      (L.openMixedTransitionOn f.left j l W hWj hWl : Γ(Y.carrier, W))) q at hv
  rw [Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_mul, Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_mul,
    ← Line.Bundles.AlgebraicLineBundle.openMixedPointTransition_restrict, ← Line.Bundles.AlgebraicLineBundle.pointTransition_restrict,
    hu, ← Line.Bundles.AlgebraicLineBundle.openMixedPointTransition_restrict] at hv
  apply (eq_div_iff (L.openMixedTransitionPair_ne_zero f i k ⟨p, hi, hk⟩)).mpr
  exact (mul_comm _ _).trans hv

end AlgebraicLineBundle

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Open.AnalyticGauge
