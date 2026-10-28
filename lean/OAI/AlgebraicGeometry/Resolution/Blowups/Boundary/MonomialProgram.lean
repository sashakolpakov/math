import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CompatibleMonomialSequence
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.IncidenceTrace

/-! # Monomial Program -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary

noncomputable section

section

/-! A monomial schedule records actual boundary-intersection blowups and their exact incidence trace. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def MonomialSchedule.Construction.BoundaryMonomialSchedule.incidenceTrace {b : ℕ} {β : Type} {a : β → ℕ}
    {L : List (Finset β)} (S : MonomialSchedule.Construction.BoundaryMonomialSchedule b β a L) : IncidenceTrace.Construction.BoundaryIncidenceTrace β := by
  induction S with
  | terminal => exact .stop _
  | step C _ _ _ ih => exact .step C ih

inductive MonomialProgram.Construction.BoundaryMonomialProgram (b : ℕ) :
    ∀ (β : Type) [Fintype β] (a : β → ℕ) (L : List (Finset β)),
      MonomialSchedule.Construction.BoundaryMonomialSchedule b β a L →
      (X : Scheme) → (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) → (J : X.IdealSheafData) → (β → X.IdealSheafData) →
      (Y : Scheme) → (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) → (K : Y.IdealSheafData) →
      Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K → Prop
  | terminal {β : Type} [Fintype β] {a : β → ℕ} {L : List (Finset β)}
      (ht : ∀ S ∈ L, MonomialSchedule.Construction.boundaryFaceWeight a S < b)
      {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f]
      {J : X.IdealSheafData} {D : β → X.IdealSheafData}
      (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L) (hJ : J = Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) :
      BoundaryMonomialProgram b β a L (.terminal ht) X f J D X f J .stop
  | step {β : Type} [Fintype β] [DecidableEq β] {a : β → ℕ} {L : List (Finset β)}
      (C : Finset β) (hC : MonomialTermination.Construction.MinimalMonomialCenter a b C) (hface : ∃ S ∈ L, C ⊆ S)
      (rest : MonomialSchedule.Construction.BoundaryMonomialSchedule b (Option β) (MonomialSchedule.Construction.boundaryScheduleExponents a b C)
        (MonomialSchedule.Construction.boundaryScheduleFaces C L))
      {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {J : X.IdealSheafData} {D : β → X.IdealSheafData}
      (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L) (hJ : J = Global.MixedBoundary.Construction.boundaryMonomialSheaf D a)
      (hI : GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C ≠ ⊥) (hb : 0 < b)
      (hp : J ≤ GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C ^ b)
      {Y : Scheme} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData}
      (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b (GlobalBlowup.Data.Construction.globalBlowup (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C) hI)
        (GlobalBlowup.Data.Construction.globalBlowupToBase (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C) hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C) J hI b) Y g K)
      (tail : BoundaryMonomialProgram b (Option β) (MonomialSchedule.Construction.boundaryScheduleExponents a b C)
        (MonomialSchedule.Construction.boundaryScheduleFaces C L) rest _ _ _
        (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C) hI D) Y g K P) :
      BoundaryMonomialProgram b β a L (.step C hC hface rest) X f J D Y g K
        (.blowup (GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C) hI hb hp
          (A.intersection_smooth f D L C) (A.intersection_blowup_smooth C hI) P)

namespace MonomialProgram.Construction.BoundaryMonomialProgram

theorem hasIncidenceTrace {b : ℕ} {β : Type} [Fintype β] {a : β → ℕ}
    {L : List (Finset β)} {S : MonomialSchedule.Construction.BoundaryMonomialSchedule b β a L}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K}
    (H : Construction.BoundaryMonomialProgram b β a L S X f J D Y g K P) :
    P.HasIncidenceTrace β D S.incidenceTrace := by
  induction H with
  | terminal ht A hJ => exact ⟨A.unitCenter.boundaryAtlas⟩
  | step C hC hface rest A hJ hI hb hp P tail ih =>
      exact ⟨⟨A.intersectionCenterAtlas C, fun _ => rfl⟩, ih⟩

theorem terminal_order {b : ℕ} (hb : 0 < b) {β : Type} [Fintype β] {a : β → ℕ}
    {L : List (Finset β)} {S : MonomialSchedule.Construction.BoundaryMonomialSchedule b β a L}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K}
    (H : Construction.BoundaryMonomialProgram b β a L S X f J D Y g K P) :
    letI : Smooth g := P.endpoint_smooth
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K (b - 1) = ⊤ := by
  induction H with
  | terminal ht A hJ =>
      rw [hJ]
      exact A.monomial_terminal _ _ _ _ b hb ht
  | step C hC hface rest A hJ hI hb hp P tail ih => exact ih

end MonomialProgram.Construction.BoundaryMonomialProgram

end

/-! Every finite monomial schedule has a recorded realization on a native boundary atlas. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem MonomialSchedule.Construction.BoundaryMonomialSchedule.exists_program {b : ℕ} (hb : 0 < b)
    {β : Type} {a : β → ℕ} {L : List (Finset β)} (S : MonomialSchedule.Construction.BoundaryMonomialSchedule b β a L) :
    ∀ (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
      (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] [Fintype β] (D : β → X.IdealSheafData)
      (J : X.IdealSheafData), J = Global.MixedBoundary.Construction.boundaryMonomialSheaf D a →
      (∀ j, D j ≠ ⊥) → Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L →
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
        (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K),
        MonomialProgram.Construction.BoundaryMonomialProgram b β a L S X f J D Y g K P := by
  induction S with
  | terminal ht =>
      intro X _ _ f _ _ D J hJ _ A
      exact ⟨X, f, J, .stop, .terminal ht A hJ⟩
  | @step β a L inst C hC hface rest ih =>
      intro X _ _ f _ _ D J hJ hD A
      let I := GlobalBoundary.Intersection.Construction.boundaryIntersectionSheaf D C
      have hI : I ≠ ⊥ := GlobalBoundary.MonomialTransform.Construction.boundaryIntersectionSheaf_ne_bot D C hC.1 hD
      have hp : J ≤ I ^ b := hJ ▸ GlobalBoundary.MonomialTransform.Construction.boundaryMonomialSheaf_permissible D a C b hC.2.1
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := A.intersection_blowup_smooth C hI
      let D' := CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D
      have he : D' = Global.MixedBoundary.Construction.globalBlowupMixedBoundary I hI D C := A.intersection_canonical_eq_mixed C hI
      have hD' : ∀ j, D' j ≠ ⊥ := by
        rw [he]
        exact Global.MixedBoundary.Construction.globalBlowupMixedBoundary_ne_bot I hI D C hD
      have A' : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) D'
          (MonomialSchedule.Construction.boundaryScheduleFaces C L) := by
        rw [he]
        exact A.blowupIntersection C hI
      have hJ' : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b =
          Global.MixedBoundary.Construction.boundaryMonomialSheaf D' (MonomialSchedule.Construction.boundaryScheduleExponents a b C) := by
        rw [hJ, he]
        exact A.monomial_transform C hI a b hC.2.1
      obtain ⟨Y, g, K, P, hP⟩ := ih (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        D' (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b) hJ' hD' A'
      exact ⟨Y, g, K, _, .step C hC hface rest A hJ hI hb hp P hP⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary
