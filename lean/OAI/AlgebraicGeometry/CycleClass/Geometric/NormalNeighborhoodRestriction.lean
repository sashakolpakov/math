import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalBallRestriction
import OAI.AlgebraicGeometry.CycleClass.Geometric.NormalProductCohomology

/-! # Normal Neighborhood Restriction -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.NormalNeighborhoodRestriction.Cycles

noncomputable section

/-!
# Restriction between genuine normal product neighborhoods

The comparison with the full normal vector space is induced by the actual
normal projection. Closed-support excision in the normal factor and a
contraction of the tangential ball prove that this map is invertible.
Consequently restriction to smaller product balls is invertible as well.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E]
  (F : Type) [NormedAddCommGroup F]

/-- Projection from the actual product of balls into the full normal space. -/
def normalProductBallProjection (r s : ℝ) :
    TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : F) s) ⟶ TopCat.of F :=
  NormalProductPair.Cycles.normalProductProjection (Metric.ball (0 : E) r) (Metric.ball (0 : F) s) ≫
    NormalBallRestriction.Cycles.normalBallInclusion F s

@[simp]
theorem normalProductBallProjection_apply (r s : ℝ)
    (z : Metric.ball (0 : E) r × Metric.ball (0 : F) s) :
    normalProductBallProjection E F r s z = z.2.val := rfl

/-- Normal projection preserves the actual complements of the zero slices. -/
theorem normalProductBallProjection_mapsTo (r s : ℝ) (hs : 0 < s) :
    Set.MapsTo (normalProductBallProjection E F r s)
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : F) s)
        (NormalBallRestriction.Cycles.normalBallCenter F s hs)) ({0}ᶜ : Set F) := by
  intro z hz
  exact NormalBallRestriction.Cycles.normalBallInclusion_mapsTo F s hs
    (NormalProductPair.Cycles.normalProductProjection_mapsTo (Metric.ball (0 : E) r)
      (Metric.ball (0 : F) s) (NormalBallRestriction.Cycles.normalBallCenter F s hs) hz)

/-- The actual rational relative-cohomology pullback along normal projection. -/
def normalProductBallCohomologyMap (r s : ℝ) (hs : 0 < s) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of F) ({0}ᶜ : Set F) n ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : F) s))
        (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : F) s)
          (NormalBallRestriction.Cycles.normalBallCenter F s hs)) n :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (normalProductBallProjection E F r s)
    (normalProductBallProjection_mapsTo E F r s hs) n

/-- Excision in the normal ball and contraction in the tangential ball give
an isomorphism whose map is the actual full normal projection. -/
def normalProductBallCohomologyIso [NormedSpace ℝ E]
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of F) ({0}ᶜ : Set F) n ≅
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : F) s))
        (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : F) s)
          (NormalBallRestriction.Cycles.normalBallCenter F s hs)) n :=
  NormalBallRestriction.Cycles.normalBallRestrictionIso F s hs n ≪≫
    NormalProductCohomology.Cycles.normalOpenBallProductCohomologyIso (ModuleCat.of ℚ ℚ) E (Metric.ball (0 : F) s)
      r hr (NormalBallRestriction.Cycles.normalBallCenter F s hs) n

@[simp]
theorem normalProductBallCohomologyIso_hom [NormedSpace ℝ E] (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (n : ℕ) :
    (normalProductBallCohomologyIso E F r s hr hs n).hom =
      normalProductBallCohomologyMap E F r s hs n := by
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (NormalBallRestriction.Cycles.normalBallInclusion F s)
      (NormalBallRestriction.Cycles.normalBallInclusion_mapsTo F s hs) n ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (NormalProductPair.Cycles.normalProductProjection (Metric.ball (0 : E) r) (Metric.ball (0 : F) s))
      (NormalProductPair.Cycles.normalProductProjection_mapsTo (Metric.ball (0 : E) r)
        (Metric.ball (0 : F) s) (NormalBallRestriction.Cycles.normalBallCenter F s hs)) n = _
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  rfl

/-- The normal-coordinate pullback itself is invertible. -/
theorem normalProductBallCohomologyMap_isIso [NormedSpace ℝ E] (r s : ℝ)
    (hr : 0 < r) (hs : 0 < s) (n : ℕ) :
    IsIso (normalProductBallCohomologyMap E F r s hs n) := by
  rw [← normalProductBallCohomologyIso_hom E F r s hr hs n]
  infer_instance

/-- The actual inclusion of two nested products of concentric balls. -/
def normalProductBallRadiusInclusion {r r' s s' : ℝ} (hr : r' ≤ r) (hs : s' ≤ s) :
    TopCat.of (Metric.ball (0 : E) r' × Metric.ball (0 : F) s') ⟶
      TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : F) s) :=
  TopCat.ofHom ⟨fun z => (NormalBallRestriction.Cycles.normalBallRadiusInclusion E hr z.1,
    NormalBallRestriction.Cycles.normalBallRadiusInclusion F hs z.2), by fun_prop⟩

/-- Inclusion of product neighborhoods does not change normal coordinates. -/
@[reassoc (attr := simp)]
theorem normalProductBallRadiusInclusion_comp {r r' s s' : ℝ}
    (hr : r' ≤ r) (hs : s' ≤ s) :
    normalProductBallRadiusInclusion E F hr hs ≫ normalProductBallProjection E F r s =
      normalProductBallProjection E F r' s' := by
  ext z
  rfl

theorem normalProductBallRadiusInclusion_mapsTo {r r' s s' : ℝ}
    (hspos : 0 < s) (hs'pos : 0 < s') (hr : r' ≤ r) (hs : s' ≤ s) :
    Set.MapsTo (normalProductBallRadiusInclusion E F hr hs)
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r') (Metric.ball (0 : F) s')
        (NormalBallRestriction.Cycles.normalBallCenter F s' hs'pos))
      (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : F) s)
        (NormalBallRestriction.Cycles.normalBallCenter F s hspos)) := by
  intro z hz h
  apply hz
  apply Subtype.ext
  exact congrArg (fun t : Metric.ball (0 : F) s => t.val) h

/-- Actual restriction between the rational cohomology groups of product pairs. -/
def normalProductBallCohomologyRestriction {r r' s s' : ℝ}
    (hspos : 0 < s) (hs'pos : 0 < s') (hr : r' ≤ r) (hs : s' ≤ s) (n : ℕ) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (Metric.ball (0 : E) r × Metric.ball (0 : F) s))
        (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r) (Metric.ball (0 : F) s)
          (NormalBallRestriction.Cycles.normalBallCenter F s hspos)) n ⟶
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ)
        (TopCat.of (Metric.ball (0 : E) r' × Metric.ball (0 : F) s'))
        (NormalProductPair.Cycles.normalProductComplement (Metric.ball (0 : E) r') (Metric.ball (0 : F) s')
          (NormalBallRestriction.Cycles.normalBallCenter F s' hs'pos)) n :=
  AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
    (normalProductBallRadiusInclusion E F hr hs)
    (normalProductBallRadiusInclusion_mapsTo E F hspos hs'pos hr hs) n

/-- Normal-coordinate pullback commutes with actual neighborhood restriction. -/
@[reassoc]
theorem normalProductBallCohomologyMap_restrict {r r' s s' : ℝ}
    (hspos : 0 < s) (hs'pos : 0 < s') (hr : r' ≤ r) (hs : s' ≤ s) (n : ℕ) :
    normalProductBallCohomologyMap E F r s hspos n ≫
        normalProductBallCohomologyRestriction E F hspos hs'pos hr hs n =
      normalProductBallCohomologyMap E F r' s' hs'pos n := by
  change AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (normalProductBallProjection E F r s) _ n ≫
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ)
      (normalProductBallRadiusInclusion E F hr hs) _ n = _
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp]
  unfold normalProductBallCohomologyMap
  congr 1

/-- Every positive-radius shrinking of both factors induces an isomorphism
on the genuine relative cohomology groups. -/
theorem normalProductBallCohomologyRestriction_isIso [NormedSpace ℝ E] {r r' s s' : ℝ}
    (hrpos : 0 < r) (hr'pos : 0 < r') (hspos : 0 < s) (hs'pos : 0 < s')
    (hr : r' ≤ r) (hs : s' ≤ s) (n : ℕ) :
    IsIso (normalProductBallCohomologyRestriction E F hspos hs'pos hr hs n) := by
  have := normalProductBallCohomologyMap_isIso E F r s hrpos hspos n
  have := normalProductBallCohomologyMap_isIso E F r' s' hr'pos hs'pos n
  have : IsIso (normalProductBallCohomologyMap E F r s hspos n ≫
      normalProductBallCohomologyRestriction E F hspos hs'pos hr hs n) := by
    rw [normalProductBallCohomologyMap_restrict]
    infer_instance
  exact IsIso.of_isIso_comp_left (normalProductBallCohomologyMap E F r s hspos n) _

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.NormalNeighborhoodRestriction.Cycles
