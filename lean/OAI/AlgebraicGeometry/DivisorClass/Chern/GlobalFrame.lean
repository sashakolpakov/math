import OAI.AlgebraicGeometry.DivisorClass.Chern.MixedAnalyticFrames

/-! # Global Frame -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-!
# ChernClass: transition functions of a globally trivial algebraic line bundle

A genuine global sheaf trivialization expresses every transition as the
ratio of the global coordinates of its local generators.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)
variable (e : L.sheaf ≅ Line.Bundles.Construction.structureModule X.carrier)

/-- The global trivialization on the actual module of sections over any open. -/
def Line.Bundles.AlgebraicLineBundle.globalSectionFrame (U : X.carrier.Opens) :
    Γ(L.sheaf, U) ≃ₗ[Γ(X.carrier, U)] Γ(X.carrier, U) := FramesFrame.Construction.moduleSheafSectionIso e U

theorem Line.Bundles.AlgebraicLineBundle.globalSectionFrame_naturality {V U : X.carrier.Opens} (h : V ≤ U) (m : Γ(L.sheaf, U)) :
    L.globalSectionFrame e V (L.sheaf.presheaf.map (homOfLE h).op m) =
      X.carrier.presheaf.map (homOfLE h).op (L.globalSectionFrame e U m) :=
  FramesFrame.Construction.moduleSheafSectionIso_naturality e h m

/-- The global coordinate of the local generator is an actual regular unit. -/
def Line.Bundles.AlgebraicLineBundle.globalFrameUnit (i : X.carrier) (U : X.carrier.Opens) (h : U ≤ L.trivializingOpen i) :
    Γ(X.carrier, U)ˣ := FramesFrame.Construction.frameTransitionUnit (L.globalSectionFrame e U) (L.sectionFrame i U h)

theorem Line.Bundles.AlgebraicLineBundle.globalFrameUnit_restrict (i : X.carrier) {V U : X.carrier.Opens}
    (hVU : V ≤ U) (hi : U ≤ L.trivializingOpen i) :
    Units.map (X.carrier.presheaf.map (homOfLE hVU).op).hom.toMonoidHom (L.globalFrameUnit e i U hi) =
      L.globalFrameUnit e i V (hVU.trans hi) :=
  FramesFrame.Construction.frameTransitionUnit_map (X.carrier.presheaf.map (homOfLE hVU).op).hom
    (L.sheaf.presheaf.map (homOfLE hVU).op)
    (L.globalSectionFrame e U) (L.sectionFrame i U hi)
    (L.globalSectionFrame e V) (L.sectionFrame i V (hVU.trans hi))
    (L.globalSectionFrame_naturality e hVU) (L.sectionFrame_naturality i hVU hi)

theorem Line.Bundles.AlgebraicLineBundle.globalFrameUnit_transition (i j : X.carrier) (U : X.carrier.Opens)
    (hi : U ≤ L.trivializingOpen i) (hj : U ≤ L.trivializingOpen j) :
    L.globalFrameUnit e i U hi * L.ambientTransitionOn i j U hi hj = L.globalFrameUnit e j U hj :=
  FramesFrame.Construction.frameTransitionUnit_cocycle (L.globalSectionFrame e U) (L.sectionFrame i U hi) (L.sectionFrame j U hj)

/-- The analytic global coordinate of a local generator. -/
def Line.Bundles.AlgebraicLineBundle.globalFrameCoordinate (i : X.carrier) : C(L.analyticCover i, ℂ) :=
  Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X (L.trivializingOpen i)
    (L.globalFrameUnit e i (L.trivializingOpen i) le_rfl : Γ(X.carrier, L.trivializingOpen i))

theorem Line.Bundles.AlgebraicLineBundle.globalFrameCoordinate_ne_zero (i : X.carrier) (p : L.analyticCover i) :
    L.globalFrameCoordinate e i p ≠ 0 := Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_unit_ne_zero X _ _ _

theorem Line.Bundles.AlgebraicLineBundle.globalFrameCoordinate_restrict (i : X.carrier) (U : X.carrier.Opens)
    (hi : U ≤ L.trivializingOpen i) (p : Line.Bundles.AlgebraicLineBundle.analyticOpen X U) :
    L.globalFrameCoordinate e i ⟨p.val, hi p.property⟩ =
      Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U (L.globalFrameUnit e i U hi : Γ(X.carrier, U)) p := by
  have hu := congrArg Units.val (L.globalFrameUnit_restrict e i hi le_rfl)
  have he := Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_restrict X hi
    (L.globalFrameUnit e i (L.trivializingOpen i) le_rfl : Γ(X.carrier, L.trivializingOpen i)) p
  change X.carrier.presheaf.map (homOfLE hi).op _ = (L.globalFrameUnit e i U hi : Γ(X.carrier, U)) at hu
  rw [hu] at he
  exact he.symm

/-- A globally trivial bundle's actual analytic transition is a ratio of global coordinates. -/
theorem Line.Bundles.AlgebraicLineBundle.pointTransition_global_ratio (i j : X.carrier) (p : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X.toOver)
    (hi : p ∈ L.analyticCover i) (hj : p ∈ L.analyticCover j) :
    L.pointTransition i j p hi hj =
      L.globalFrameCoordinate e j ⟨p, hj⟩ / L.globalFrameCoordinate e i ⟨p, hi⟩ := by
  let U := L.trivializingOpen i ⊓ L.trivializingOpen j
  let q : Line.Bundles.AlgebraicLineBundle.analyticOpen X U := ⟨p, hi, hj⟩
  have h := congrArg (fun u : Γ(X.carrier, U)ˣ =>
    Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U (u : Γ(X.carrier, U)) q)
    (L.globalFrameUnit_transition e i j U inf_le_left inf_le_right)
  change Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U ((L.globalFrameUnit e i U inf_le_left : Γ(X.carrier, U)) *
    (L.ambientTransitionOn i j U inf_le_left inf_le_right : Γ(X.carrier, U))) q =
      Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn X U (L.globalFrameUnit e j U inf_le_right : Γ(X.carrier, U)) q at h
  rw [Line.Bundles.AlgebraicLineBundle.sectionEvaluationOn_mul, ← Line.Bundles.AlgebraicLineBundle.globalFrameCoordinate_restrict,
    ← Line.Bundles.AlgebraicLineBundle.pointTransition_restrict, ← Line.Bundles.AlgebraicLineBundle.globalFrameCoordinate_restrict] at h
  apply (eq_div_iff (L.globalFrameCoordinate_ne_zero e i ⟨p, hi⟩)).mpr
  exact (mul_comm _ _).trans h

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
