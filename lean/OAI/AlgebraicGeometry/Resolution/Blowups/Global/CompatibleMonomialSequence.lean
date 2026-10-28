import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.IntersectionCanonical
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.IntegralSequenceReplacement
import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.CenterSequenceReplacement

/-! # Compatible Monomial Sequence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Global monomial resolution retains the full canonical boundary, with integral-center replacements on compact ambient schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Boundary.MonomialSchedule.Construction.BoundaryMonomialSchedule.global_boundary_sequence {b : ℕ} (hb : 0 < b)
    {β : Type} {a : β → ℕ} {L : List (Finset β)} (T : Boundary.MonomialSchedule.Construction.BoundaryMonomialSchedule b β a L) :
    ∀ (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
      (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] [Fintype β] (D : β → X.IdealSheafData),
      (∀ j, D j ≠ ⊥) → Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L →
      ∃ S : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a), S.boundaryCompatible β D := by
  induction T with
  | terminal ht =>
      intro X _ _ f _ _ D _ A
      refine ⟨.terminal (Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.monomial_terminal f D _ A _ b hb ht), ?_⟩
      exact ⟨A.unitCenter.boundaryAtlas⟩
  | @step β a L inst C hC _ rest ih =>
      intro X _ _ f _ _ D hD A
      let I := GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C
      have hI : I ≠ ⊥ := GlobalBoundary.MonomialTransform.Construction.boundaryIntersectionSheaf_ne_bot D C hC.1 hD
      have hblowup : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := A.intersection_blowup_smooth C hI
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := hblowup
      let D' := Global.MixedBoundary.Construction.globalBlowupMixedBoundary I hI D C
      let A' := A.blowupIntersection C hI
      obtain ⟨tail, htail⟩ := ih (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) D'
        (Global.MixedBoundary.Construction.globalBlowupMixedBoundary_ne_bot I hI D C hD) A'
      have hnext : ∃ S : Global.MonomialSequence.Construction.SmoothFixedControlSequence b (GlobalBlowup.Data.Construction.globalBlowup I hI)
          (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) hI b),
          S.boundaryCompatible (Option β) D' := by
        rw [A.monomial_transform C hI a b hC.2.1]
        exact ⟨tail, htail⟩
      obtain ⟨S, hS⟩ := hnext
      refine ⟨.blowup I hI hb (GlobalBoundary.MonomialTransform.Construction.boundaryMonomialSheaf_permissible D a C b hC.2.1)
        (Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.intersection_smooth f D L A C) hblowup S, ?_⟩
      refine ⟨⟨A.intersectionCenterAtlas C⟩, ?_⟩
      rw [A.intersection_canonical_eq_mixed C hI]
      exact hS

theorem Global.CompatibleMonomialSequence.Construction.exists_global_boundary_monomial_compatible_sequence
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (hD : ∀ j, D j ≠ ⊥)
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ]) (a : β → ℕ) (b : ℕ) (hb : 0 < b) :
    ∃ T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a), T.boundaryCompatible β D := by
  obtain ⟨T⟩ := Boundary.MonomialSchedule.Construction.exists_boundary_monomial_schedule b hb (Fintype.card β) β a [Finset.univ]
    (by intro S hS; exact List.mem_singleton.mp hS ▸ le_rfl)
  exact T.global_boundary_sequence hb X f D hD A

theorem Global.CompatibleMonomialSequence.Construction.exists_global_boundary_monomial_compatible_integral_sequence
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] {β : Type} [Fintype β]
    (D : β → X.IdealSheafData) (hD : ∀ j, D j ≠ ⊥)
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ]) (a : β → ℕ) (b : ℕ) (hb : 0 < b) :
    ∃ T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a),
      T.integralCenters ∧ T.boundaryCompatible β D := by
  obtain ⟨T, hT⟩ := Global.CompatibleMonomialSequence.Construction.exists_global_boundary_monomial_compatible_sequence f D hD A a b hb
  exact T.exists_boundary_integral_replacement (Integral.CenterSequenceReplacement.Construction.boundaryMonomialSheaf_ne_bot D a hD) β D hT

end

end OAI.AlgebraicGeometry.Resolution.Blowups
