import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FiniteTargetFibers

/-! # Finite Fiber Descent -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FiniteFiberDescent

noncomputable section

/-! Finiteness after any base change detects finite target fibers above
its image. Residue fields of lifted target points supply the necessary
field extensions; no chosen compatibility of algebraic closures is used. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {X Y B T : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ B) (g : T ⟶ B)

theorem finite_target_fiber_of_finite_baseChange
    (h : IsFinite (HilbertScheme.Presentations.Relative.MorphismIsomorphismLocus.relativeMorphismBaseChange f q g)) (y : Y)
    (hy : q y ∈ Set.range g) : (f ⁻¹' {y}).Finite := by
  have hi : IsFinite (pullback.fst (pullback.fst q g) f) := by
    rw [← IntegralModel.Finite.PullbackTransport.finite_pullback_snd_iff_fst, ← IntegralModel.Finite.PullbackTransport.relativeMorphismBaseChange_isFinite_iff]
    exact h
  have hyr : y ∈ Set.range (pullback.fst q g) := by
    rw [Scheme.Pullback.range_fst]
    exact hy
  obtain ⟨z, hz⟩ := hyr
  let c := (pullback q g).fromSpecResidueField z
  let a := c ≫ pullback.fst q g
  have ha : Set.range a = {y} := by
    ext w
    constructor
    · rintro ⟨t, rfl⟩
      change (pullback.fst q g) (c t) = y
      rw [show c t = z from (pullback q g).fromSpecResidueField_apply z t, hz]
    · intro hw
      change w = y at hw
      subst w
      refine ⟨IsLocalRing.closedPoint ((pullback q g).residueField z), ?_⟩
      change (pullback.fst q g) (c _) = y
      rw [show c _ = z from (pullback q g).fromSpecResidueField_apply z _, hz]
  have : IsFinite (pullback.fst a f) :=
    (IntegralModel.Finite.PullbackTransport.finite_pullback_fst_iterated_iff (pullback.fst q g) f c).mp inferInstance
  have : IsFinite (pullback.snd f a) := (IntegralModel.Finite.PullbackTransport.finite_pullback_snd_iff_fst f a).mpr inferInstance
  have hfin := (pullback.snd f a).finite_preimage Set.finite_univ
  have : Finite (pullback f a : Scheme.{u}) :=
    Set.finite_univ_iff.mp (by simpa only [Set.preimage_univ] using hfin)
  have hr := Set.finite_range (pullback.fst f a)
  rwa [Scheme.Pullback.range_fst, ha] at hr

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Relative.FiniteFiberDescent
