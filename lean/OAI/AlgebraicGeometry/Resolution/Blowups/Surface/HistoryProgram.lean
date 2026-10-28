import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.HistorySchedule
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.AuxiliaryHistoryOpen
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonOpen
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.FixedLabelComposition

/-! # History Program -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface.HistoryProgram.Construction

noncomputable section

/-! A recorded history program combines auxiliary clearing, a continuation on the cleared-boundary complement, and its actual ambient extension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

inductive SurfaceHistoryProgram (n : ℕ) :
    {β γ : Type} → [Fintype β] → [Fintype γ] → [DecidableEq β] → {e : γ ↪ β} →
    HistorySchedule.Construction.SurfaceHistorySchedule n e →
    (X : Scheme) → (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) → (J : X.IdealSheafData) → (β → X.IdealSheafData) →
    (Y : Scheme) → (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) → (K : Y.IdealSheafData) →
    Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K → Prop
  | full {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β]
      (e : γ ↪ β) (he : Function.Surjective e) (ℓ : ℕ)
      {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
      {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
      (T : LogarithmicProgram.Construction.SurfaceLogarithmicProgram n ℓ β X f J D Y g K P) :
      SurfaceHistoryProgram n (.full e he ℓ) X f J D Y g K P
  | clear {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β]
      (e : γ ↪ β) (j : β) (hj : ∀ s, j ≠ e s) (ℓ : ℕ)
      (schedule : HistorySchedule.Construction.SurfaceHistorySchedule n
        (FixedLengthBoundaryHistory.Construction.iteratedExtendedBoundaryHistory (HistorySchedule.Construction.surfaceAuxiliaryProgramStepCount n ℓ (Fintype.card β)) e j hj))
      {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {J : X.IdealSheafData} {C J' : Y.IdealSheafData} {D : β → X.IdealSheafData}
      (A : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) (n + 1)) Y g C)
      (aux : AuxiliaryProgram.Construction.SurfaceAuxiliaryProgram n ℓ β X f J D j Y g C A)
      (hA : A.uniformBoundaryCompatible β D)
      (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g J') (same : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups (n + 1) (n + 1) A P)
      {V Z : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {L : V.IdealSheafData} {M : Z.IdealSheafData}
      (T : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (A.transformedBoundaryComplement D j)
        ((A.transformedBoundaryComplement D j).ι ≫ g) (J'.comap (A.transformedBoundaryComplement D j).ι) V h L)
      (tail : SurfaceHistoryProgram n schedule (A.transformedBoundaryComplement D j)
        ((A.transformedBoundaryComplement D j).ι ≫ g) (J'.comap (A.transformedBoundaryComplement D j).ι)
        (fun l => (A.boundaryAtLength D _ aux.stepCount l).comap (A.transformedBoundaryComplement D j).ι) V h L T)
      (R : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) Y g J' Z k M) (r : V ⟶ Z)
      (comparison : R.EtaleComparison T (A.transformedBoundaryComplement D j).ι r)
      (hR : R.uniformBoundaryCompatible (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels (HistorySchedule.Construction.surfaceAuxiliaryProgramStepCount n ℓ (Fintype.card β)) β)
        (A.boundaryAtLength D _ aux.stepCount))
      (hcover : letI : Smooth k := R.endpoint_smooth
        ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf k M n).support : Set Z) ⊆ Set.range r) :
      SurfaceHistoryProgram n (.clear e j hj ℓ schedule) X f J D Z k M (P.append R)

namespace SurfaceHistoryProgram

theorem uniformBoundaryCompatible
    {n : ℕ} {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] {e : γ ↪ β}
    {schedule : HistorySchedule.Construction.SurfaceHistorySchedule n e} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : Construction.SurfaceHistoryProgram n schedule X f J D Y g K P) : P.uniformBoundaryCompatible β D := by
  cases T with
  | full e he ℓ T => exact T.uniformBoundaryCompatible
  | clear e j hj ℓ schedule A aux hA P same T tail R r comparison hR hcover =>
      have hP := same.uniformBoundaryCompatible _ _ hA
      have hcount := same.stepCount_eq.symm.trans aux.stepCount
      have hboundary := same.boundaryAtLength β D _ aux.stepCount hcount
      apply P.append_uniformBoundaryCompatible_fixed_labels R _ hP _ hcount
      rw [← hboundary]
      exact hR

theorem terminal_order
    {n : ℕ} {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] {e : γ ↪ β}
    {schedule : HistorySchedule.Construction.SurfaceHistorySchedule n e} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : Construction.SurfaceHistoryProgram n schedule X f J D Y g K P) :
    letI : Smooth g := P.endpoint_smooth
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K n = ⊤ := by
  induction T with
  | full e he ℓ T => exact T.terminal_order
  | clear e j hj ℓ schedule A aux hA P same T tail R r comparison hR hcover ih =>
      exact comparison.terminal_order_of_endpoint_cover R T _ r n hcover ih

theorem stepCount
    {n : ℕ} {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] {e : γ ↪ β}
    {schedule : HistorySchedule.Construction.SurfaceHistorySchedule n e} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : Construction.SurfaceHistoryProgram n schedule X f J D Y g K P) : P.stepCount = schedule.stepCount := by
  induction T with
  | full e he ℓ T => exact T.stepCount
  | clear e j hj ℓ schedule A aux hA P same T tail R r comparison hR hcover ih =>
      rw [Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.append_stepCount, ← same.stepCount_eq, aux.stepCount,
        comparison.stepCount_eq R T _ r, ih]
      rfl

end SurfaceHistoryProgram

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface.HistoryProgram.Construction
