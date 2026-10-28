import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.AtlasBlowup

/-! # Monomial Sequence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Finite actual global smooth blowup sequences clearing labelled monomial ideals at fixed control. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- Every step is the actual native global blowup of a nonzero permissible
smooth center. The control stays fixed and the final order locus is empty. -/
inductive Global.MonomialSequence.Construction.SmoothFixedControlSequence (b : ℕ) :
    (X : Scheme) → (X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) → X.IdealSheafData → Type 1
  | terminal {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {J : X.IdealSheafData}
      (hterminal : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1) = ⊤) :
      SmoothFixedControlSequence b X f J
  | blowup {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
      {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData}
      (I : X.IdealSheafData) (hI : I ≠ ⊥) (hb : 0 < b) (hperm : J ≤ I ^ b)
      (hsmooth : Smooth (I.subschemeι ≫ f))
      (hblowup : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
      (tail : SmoothFixedControlSequence b (GlobalBlowup.Data.Construction.globalBlowup I hI)
        (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b)) :
      SmoothFixedControlSequence b X f J

/-- The schedule produces one global sequence. All native ideal sheaves,
their local equations, and the remaining faces propagate through each step. -/
theorem Boundary.MonomialSchedule.Construction.BoundaryMonomialSchedule.global_sequence {b : ℕ} (hb : 0 < b)
    {β : Type} {a : β → ℕ} {L : List (Finset β)} (T : Boundary.MonomialSchedule.Construction.BoundaryMonomialSchedule b β a L) :
    ∀ (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
      (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] [Fintype β] (D : β → X.IdealSheafData),
      (∀ j, D j ≠ ⊥) → Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L →
      Nonempty (Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a)) := by
  induction T with
  | terminal ht =>
      intro X _ _ f _ _ D _ A
      exact ⟨.terminal (Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.monomial_terminal f D _ A _ b hb ht)⟩
  | @step β a L inst C hC _ rest ih =>
      intro X _ _ f _ _ D hD A
      let I := GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C
      have hI : I ≠ ⊥ := GlobalBoundary.MonomialTransform.Construction.boundaryIntersectionSheaf_ne_bot D C hC.1 hD
      have hblowup : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := A.intersection_blowup_smooth C hI
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := hblowup
      let D' := Global.MixedBoundary.Construction.globalBlowupMixedBoundary I hI D C
      let A' := A.blowupIntersection C hI
      obtain ⟨tail⟩ := ih (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) D'
        (Global.MixedBoundary.Construction.globalBlowupMixedBoundary_ne_bot I hI D C hD) A'
      refine ⟨.blowup I hI hb (GlobalBoundary.MonomialTransform.Construction.boundaryMonomialSheaf_permissible D a C b hC.2.1)
        (Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas.intersection_smooth f D L A C) hblowup ?_⟩
      rw [A.monomial_transform C hI a b hC.2.1]
      exact tail

/-- On every smooth integral complex scheme with a displayed finite labelled
normal-crossing boundary, every boundary monomial has a finite global smooth
blowup sequence clearing its order at the prescribed positive control. -/
theorem Global.MonomialSequence.Construction.exists_global_boundary_monomial_sequence
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    {β : Type} [Fintype β] (D : β → X.IdealSheafData) (hD : ∀ j, D j ≠ ⊥)
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ]) (a : β → ℕ) (b : ℕ) (hb : 0 < b) :
    Nonempty (Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a)) := by
  obtain ⟨T⟩ := Boundary.MonomialSchedule.Construction.exists_boundary_monomial_schedule b hb (Fintype.card β) β a [Finset.univ]
    (by
      intro S hS
      have he := List.mem_singleton.mp hS
      subst S
      exact le_rfl)
  exact T.global_sequence hb X f D hD A

end

end OAI.AlgebraicGeometry.Resolution.Blowups
