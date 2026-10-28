import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.TargetBaseChangeIsomorphism
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Isomorphism Target Fibers -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.IsomorphismTargetFibers

noncomputable section

/-! An isomorphic coefficient fiber gives isomorphic fibers over each
target point; properness then gives finite target neighborhoods. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y B : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ B)

theorem isIso_targetFiber_of_relative_fiber (y : Y)
    (h : IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange f q (B.fromSpecResidueField (q y)))) :
    IsIso (f.fiberToSpecResidueField y) := by
  have hi : IsIso (pullback.fst (pullback.fst q (B.fromSpecResidueField (q y))) f) := by
    rw [← SourceIsomorphismTransport.isIso_pullback_snd_iff_fst, ← MorphismIsomorphismLocus.relativeMorphismBaseChange_isIso_iff]
    exact h
  let k : Spec (Y.residueField y) ⟶ pullback q (B.fromSpecResidueField (q y)) :=
    pullback.lift (Y.fromSpecResidueField y) (Spec.map (q.residueFieldMap y))
      (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField q y).symm
  have hk : k ≫ pullback.fst q (B.fromSpecResidueField (q y)) = Y.fromSpecResidueField y :=
    pullback.lift_fst _ _ _
  change IsIso (pullback.snd f (Y.fromSpecResidueField y))
  rw [SourceIsomorphismTransport.isIso_pullback_snd_iff_fst, ← hk, ← IteratedPullbackIsomorphism.isIso_pullback_fst_iterated_iff]
  infer_instance

theorem finite_target_fiber_of_relative_isomorphism (y : Y)
    (h : IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange f q (B.fromSpecResidueField (q y)))) :
    (f ⁻¹' {y}).Finite := by
  let := isIso_targetFiber_of_relative_fiber f q y h
  let : Finite (f.fiber y) := Finite.of_injective
    (f.fiberToSpecResidueField y) (f.fiberToSpecResidueField y).injective
  exact (f.fiberHomeo y).finite_iff.mp inferInstance

theorem exists_finite_target_neighborhood_of_relative_isomorphism
    [IsProper f] (y : Y)
    (h : IsIso (MorphismIsomorphismLocus.relativeMorphismBaseChange f q (B.fromSpecResidueField (q y)))) :
    ∃ U : Y.Opens, y ∈ U ∧ IsFinite (f ∣_ U) :=
  exists_isFinite_morphismRestrict_of_finite_preimage_singleton f y
    (finite_target_fiber_of_relative_isomorphism f q y h)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.IsomorphismTargetFibers
