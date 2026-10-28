import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Finite.PullbackTransport
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Finite Target Fibers -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FiniteTargetFibers

noncomputable section

/-! A finite coefficient fiber has finite fibers over every target
point above it. Properness then gives finite target neighborhoods. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y B : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ B)

theorem isFinite_targetFiber_of_relative_fiber (y : Y)
    (h : IsFinite (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q (B.fromSpecResidueField (q y)))) :
    IsFinite (f.fiberToSpecResidueField y) := by
  have hi : IsFinite (pullback.fst (pullback.fst q (B.fromSpecResidueField (q y))) f) := by
    rw [← IntegralModel.Finite.PullbackTransport.finite_pullback_snd_iff_fst, ← IntegralModel.Finite.PullbackTransport.relativeMorphismBaseChange_isFinite_iff]
    exact h
  let k : Spec (Y.residueField y) ⟶ pullback q (B.fromSpecResidueField (q y)) :=
    pullback.lift (Y.fromSpecResidueField y) (Spec.map (q.residueFieldMap y))
      (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField q y).symm
  have hk : k ≫ pullback.fst q (B.fromSpecResidueField (q y)) = Y.fromSpecResidueField y :=
    pullback.lift_fst _ _ _
  change IsFinite (pullback.snd f (Y.fromSpecResidueField y))
  rw [IntegralModel.Finite.PullbackTransport.finite_pullback_snd_iff_fst, ← hk, ← IntegralModel.Finite.PullbackTransport.finite_pullback_fst_iterated_iff]
  infer_instance

theorem finite_target_fiber_of_relative_finite (y : Y)
    (h : IsFinite (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q (B.fromSpecResidueField (q y)))) :
    (f ⁻¹' {y}).Finite := by
  let := isFinite_targetFiber_of_relative_fiber f q y h
  have hfin := (f.fiberToSpecResidueField y).finite_preimage Set.finite_univ
  have : Finite (f.fiber y) := Set.finite_univ_iff.mp (by simpa only [Set.preimage_univ] using hfin)
  exact (f.fiberHomeo y).finite_iff.mp inferInstance

theorem exists_finite_target_neighborhood_of_relative_finite [IsProper f] (y : Y)
    (h : IsFinite (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q (B.fromSpecResidueField (q y)))) :
    ∃ U : Y.Opens, y ∈ U ∧ IsFinite (f ∣_ U) :=
  exists_isFinite_morphismRestrict_of_finite_preimage_singleton f y
    (finite_target_fiber_of_relative_finite f q y h)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FiniteTargetFibers
