import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCohomologyExcision
import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainFunctoriality
import Mathlib.Analysis.Normed.Group.Basic

/-! # Normal Ball Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.NormalBallRestriction

noncomputable section

/-!
# Actual restriction from a punctured normal space to a punctured ball

Closed-support excision for the singleton at the origin proves that restriction
to any positive-radius open ball is an isomorphism in rational relative
cohomology. The maps are the actual pullbacks along subtype inclusions.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainFunctoriality.Cohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Cycles

variable (F : Type) [NormedAddCommGroup F]

/-- The center as an actual point of a positive-radius normal ball. -/
def normalBallCenter (r : ℝ) (hr : 0 < r) : Metric.ball (0 : F) r :=
  ⟨0, Metric.mem_ball_self hr⟩

@[simp]
theorem normalBallCenter_val (r : ℝ) (hr : 0 < r) :
    (normalBallCenter F r hr).val = 0 := rfl

/-- The actual subtype inclusion of the normal ball into the normal space. -/
abbrev normalBallInclusion (r : ℝ) :
    TopCat.of (Metric.ball (0 : F) r) ⟶ TopCat.of F :=
  LocalHomology.Cycles.subspaceInclusion (TopCat.of F) (Metric.ball (0 : F) r)

@[simp]
theorem normalBall_preimage_zero (r : ℝ) (hr : 0 < r) :
    (normalBallInclusion F r) ⁻¹' ({0} : Set F) =
      ({normalBallCenter F r hr} : Set (Metric.ball (0 : F) r)) := by
  ext x
  change x.val = 0 ↔ x = normalBallCenter F r hr
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

@[simp]
theorem normalBall_preimage_puncture (r : ℝ) (hr : 0 < r) :
    (normalBallInclusion F r) ⁻¹' ({0}ᶜ : Set F) =
      ({normalBallCenter F r hr}ᶜ : Set (Metric.ball (0 : F) r)) := by
  rw [Set.preimage_compl, normalBall_preimage_zero F r hr]

/-- The subtype inclusion is a map of the actual punctured pairs. -/
theorem normalBallInclusion_mapsTo (r : ℝ) (hr : 0 < r) :
    Set.MapsTo (normalBallInclusion F r)
      ({normalBallCenter F r hr}ᶜ : Set (Metric.ball (0 : F) r)) ({0}ᶜ : Set F) := by
  intro x hx
  change x.val ≠ 0
  intro h
  exact hx (Subtype.ext h)

/-- The actual restriction on rational relative cohomology of the punctured pair. -/
abbrev normalBallCohomologyRestriction (r : ℝ) (hr : 0 < r) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of F) ({0}ᶜ : Set F) n ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (Metric.ball (0 : F) r))
        ({normalBallCenter F r hr}ᶜ : Set (Metric.ball (0 : F) r)) n :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (normalBallInclusion F r)
    (normalBallInclusion_mapsTo F r hr) n

/-- Closed-support excision makes the actual ball restriction invertible. -/
theorem normalBallCohomologyRestriction_isIso (r : ℝ) (hr : 0 < r) (n : ℕ) :
    IsIso (normalBallCohomologyRestriction F r hr n) := by
  have transport (A : Set (Metric.ball (0 : F) r))
      (hA : A = (normalBallInclusion F r) ⁻¹' ({0}ᶜ : Set F))
      (hmap : Set.MapsTo (normalBallInclusion F r) A ({0}ᶜ : Set F)) :
      IsIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
        (normalBallInclusion F r) hmap n) := by
    subst A
    exact RelativeCohomologyExcision.Cycles.closedSupportCohomologyRestriction_isIso (TopCat.of F)
      (Metric.ball (0 : F) r) ({0} : Set F) isClosed_singleton Metric.isOpen_ball
      (Set.singleton_subset_iff.mpr (Metric.mem_ball_self hr)) n
  exact transport _ (normalBall_preimage_puncture F r hr).symm _

/-- Rational relative cohomology of the normal space restricts isomorphically
to any positive-radius punctured normal ball. -/
def normalBallRestrictionIso (r : ℝ) (hr : 0 < r) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of F) ({0}ᶜ : Set F) n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (Metric.ball (0 : F) r))
        ({normalBallCenter F r hr}ᶜ : Set (Metric.ball (0 : F) r)) n := by
  have := normalBallCohomologyRestriction_isIso F r hr n
  exact asIso (normalBallCohomologyRestriction F r hr n)

/-- The comparison map is literally pullback by the subtype inclusion of pairs. -/
@[simp]
theorem normalBallRestrictionIso_hom (r : ℝ) (hr : 0 < r) (n : ℕ) :
    (normalBallRestrictionIso F r hr n).hom =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (normalBallInclusion F r)
        (normalBallInclusion_mapsTo F r hr) n := rfl

/-- The actual inclusion of a smaller concentric normal ball into a larger one. -/
abbrev normalBallRadiusInclusion {r s : ℝ} (hrs : r ≤ s) :
    TopCat.of (Metric.ball (0 : F) r) ⟶ TopCat.of (Metric.ball (0 : F) s) :=
  LocalHomology.Cycles.subspaceMap (𝟙 (TopCat.of F)) (Metric.ball_subset_ball hrs)

@[simp]
theorem normalBallRadiusInclusion_val {r s : ℝ} (hrs : r ≤ s)
    (x : Metric.ball (0 : F) r) :
    (normalBallRadiusInclusion F hrs x).val = x.val := rfl

/-- Nested-radius inclusion followed by ambient inclusion is ambient inclusion. -/
@[reassoc (attr := simp)]
theorem normalBallRadiusInclusion_comp {r s : ℝ} (hrs : r ≤ s) :
    normalBallRadiusInclusion F hrs ≫ normalBallInclusion F s = normalBallInclusion F r := by
  ext x
  rfl

theorem normalBallRadiusInclusion_mapsTo {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) :
    Set.MapsTo (normalBallRadiusInclusion F hrs)
      ({normalBallCenter F r hr}ᶜ : Set (Metric.ball (0 : F) r))
      ({normalBallCenter F s hs}ᶜ : Set (Metric.ball (0 : F) s)) := by
  intro x hx h
  have hval : x.val = (0 : F) :=
    congrArg (fun y : Metric.ball (0 : F) s => y.val) h
  exact hx (Subtype.ext hval)

/-- The actual relative-cohomology restriction between two positive-radius balls. -/
abbrev normalBallRadiusCohomologyRestriction {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (Metric.ball (0 : F) s))
        ({normalBallCenter F s hs}ᶜ : Set (Metric.ball (0 : F) s)) n ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (Metric.ball (0 : F) r))
        ({normalBallCenter F r hr}ᶜ : Set (Metric.ball (0 : F) r)) n :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (normalBallRadiusInclusion F hrs)
    (normalBallRadiusInclusion_mapsTo F hr hs hrs) n

/-- Ambient-to-ball excision is natural for the actual restriction between nested balls. -/
@[reassoc]
theorem normalBallRestrictionIso_naturality {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) (n : ℕ) :
    (normalBallRestrictionIso F s hs n).hom ≫
        normalBallRadiusCohomologyRestriction F hr hs hrs n =
      (normalBallRestrictionIso F r hr n).hom := by
  rw [normalBallRestrictionIso_hom, normalBallRestrictionIso_hom]
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (normalBallInclusion F s) _ n ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (normalBallRadiusInclusion F hrs) _ n = _
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  rfl

/-- Restriction between nested punctured balls is itself the corresponding
composite of the canonical excision isomorphisms. -/
theorem normalBallRadiusCohomologyRestriction_eq {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) (n : ℕ) :
    normalBallRadiusCohomologyRestriction F hr hs hrs n =
      (normalBallRestrictionIso F s hs n).inv ≫ (normalBallRestrictionIso F r hr n).hom := by
  apply (cancel_epi (normalBallRestrictionIso F s hs n).hom).mp
  rw [Iso.hom_inv_id_assoc, normalBallRestrictionIso_naturality]

/-- The actual nested-ball restriction is invertible. -/
theorem normalBallRadiusCohomologyRestriction_isIso {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) (n : ℕ) :
    IsIso (normalBallRadiusCohomologyRestriction F hr hs hrs n) := by
  rw [normalBallRadiusCohomologyRestriction_eq F hr hs hrs n]
  infer_instance

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.NormalBallRestriction
