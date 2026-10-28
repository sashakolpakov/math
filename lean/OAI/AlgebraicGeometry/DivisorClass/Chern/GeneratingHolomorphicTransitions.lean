import OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingPointTransitions
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSection.SchemeDifferentiable

/-! # Generating Holomorphic Transitions -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingHolomorphicTransitions

noncomputable section

/-! The algebraized generating map gives the exact original holomorphic section ratios as the constructed algebraic bundle's frame transitions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  (u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace) {n : ℕ}
  (s : Fin (n + 1) → HolomorphicSection.Data.HolomorphicLineSection u ⊤)
  (hs : ∀ x : V.analyticSpace, ∃ j, HolomorphicSection.Nonzero.holomorphicSectionNonzeroAt u (s j) x)
  (g : V.toOver ⟶ (ComplexMultiplication.HodgeComparison.ProjectiveScheme.CM.Construction.projectiveSpaceVariety n).toOver)
  (hg : ∀ x, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x = HolomorphicSection.SchemeDifferentiable.holomorphicSectionSchemeMap V u s hs x)

include hg in
theorem generatingAlgebraicFrame_domain_iff (i : Fin (n + 1)) (x : V.analyticSpace) :
    x ∈ (GeneratingFrames.generatingAlgebraicSectionFrameAtlas V.presentation g).analyticDomain i ↔
      HolomorphicSection.Nonzero.holomorphicSectionNonzeroAt u (s i) x := by
  change (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g x).left (default : Foundations.Scheme.ProjectiveSpace.complexBase) ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i ↔ _
  have hmap := congrArg (fun q : ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n =>
    q.left (default : Foundations.Scheme.ProjectiveSpace.complexBase) ∈ Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n i) (hg x)
  exact (Iff.of_eq hmap).trans
    ((ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint_mem_coordinateOpen n i (HolomorphicSection.Projective.holomorphicSectionProjectiveMap u s hs x)).trans
      (HolomorphicSection.Projective.holomorphicSectionProjectiveMap_inPatch u s hs i x))

include hg in
theorem generatingAlgebraicFrame_holomorphic_transition (i j : Fin (n + 1)) (a : V.analyticSpace)
    (x : Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u a)
    (hi : x.val ∈ (GeneratingFrames.generatingAlgebraicSectionFrameAtlas V.presentation g).analyticDomain i)
    (hj : x.val ∈ (GeneratingFrames.generatingAlgebraicSectionFrameAtlas V.presentation g).analyticDomain j) :
    (GeneratingFrames.generatingAlgebraicSectionFrameAtlas V.presentation g).pointTransition i j x.val hi hj =
      (s j).val a ⟨x.val, trivial, x.property⟩ / (s i).val a ⟨x.val, trivial, x.property⟩ := by
  have hm := congrArg (fun q : ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemeComplexPoints n =>
    Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm q)) (hg x.val)
  have hh : Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm
      (HolomorphicSection.SchemeDifferentiable.holomorphicSectionSchemeMap V u s hs x.val)) =
      Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j (HolomorphicSection.Projective.holomorphicSectionProjectiveMap u s hs x.val) :=
    congrArg (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i j) ((ComplexPoints.Analytic.ProjectiveScheme.projectiveSchemePointHomeomorph n).symm_apply_apply _)
  exact (GeneratingPointTransitions.generatingAlgebraicFrame_pointTransition V.presentation g i j x.val hi hj).trans
    (hm.trans (hh.trans (HolomorphicSection.Projective.holomorphicSectionProjectiveMap_ratio u s hs a x i j)))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingHolomorphicTransitions
