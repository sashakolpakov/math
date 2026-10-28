import OAI.AlgebraicGeometry.Resolution.Blowups.CanonicalCenterIncidenceTrace
import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceFixedComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.LogarithmicProgram

/-! # Program Incidence Trace -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! All prescribed-level logarithmic surface programs have one exact pure incidence trace. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Surface.ProgramIncidenceTrace.Construction.boundedSurfaceIncidenceTrace (n : ℕ) : (m : ℕ) → (β : Type) → [Fintype β] → Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β
  | 0, β, _ => .stop β
  | m + 1, β, _ => if (n + 1).factorial ≤ m + 1 then
      (CanonicalCenterIncidenceTrace.Construction.canonicalCenterIncidenceTrace β).appendAtLength (Fintype.card (Finset β)) (CanonicalCenterIncidenceTrace.Construction.canonicalCenterIncidenceTrace_length β)
        (boundedSurfaceIncidenceTrace n m (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels (Fintype.card (Finset β)) β))
      else .stop β

theorem Surface.ProgramIncidenceTrace.Construction.boundedSurfaceIncidenceTrace_of_lt (n m : ℕ) (β : Type) [Fintype β] (h : m < (n + 1).factorial) :
    Surface.ProgramIncidenceTrace.Construction.boundedSurfaceIncidenceTrace n m β = .stop β := by
  cases m with
  | zero => rfl
  | succ m => exact ite_eq_right (Nat.not_le.mpr h)

theorem Surface.ProgramIncidenceTrace.Construction.boundedSurfaceIncidenceTrace_length (n m : ℕ) (β : Type) [Fintype β] :
    (Surface.ProgramIncidenceTrace.Construction.boundedSurfaceIncidenceTrace n m β).length = Uniform.IncidenceSurfaceLength.Construction.surfaceIncidenceProgramStepCount n m (Fintype.card β) := by
  classical
  induction m generalizing β with
  | zero => rfl
  | succ m ih =>
      by_cases h : (n + 1).factorial ≤ m + 1
      · rw [Surface.ProgramIncidenceTrace.Construction.boundedSurfaceIncidenceTrace, ite_eq_left h, Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.appendAtLength_length,
          ih, Uniform.IncidenceSurfaceLength.Construction.card_iteratedBoundaryLabels, Fintype.card_finset]
        exact (ite_eq_left h).symm
      · rw [Surface.ProgramIncidenceTrace.Construction.boundedSurfaceIncidenceTrace, ite_eq_right h]
        exact (ite_eq_right h).symm

theorem Uniform.IncidenceSurfaceProgram.Construction.UniformIncidenceSurfaceProgram.hasIncidenceTrace
    {n m : ℕ} {β : Type} [Fintype β] {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : Uniform.IncidenceSurfaceProgram.Construction.UniformIncidenceSurfaceProgram n m β X f J D Y g K P) :
    P.HasIncidenceTrace β D (Surface.ProgramIncidenceTrace.Construction.boundedSurfaceIncidenceTrace n m β) := by
  induction T with
  | terminal hstop E ht =>
      rw [Surface.ProgramIncidenceTrace.Construction.boundedSurfaceIncidenceTrace_of_lt _ _ _ hstop]
      exact ⟨E⟩
  | refine A hb hd hlevel AM P hcenters hcount hP Q tail ih =>
      rw [Surface.ProgramIncidenceTrace.Construction.boundedSurfaceIncidenceTrace, ite_eq_left hlevel]
      have hhead := A.surfaceIncidenceCenters_hasTrace _ hb hd hlevel _ AM P hcenters
      exact hhead.appendAtLength P Q _ _ _ (CanonicalCenterIncidenceTrace.Construction.canonicalCenterIncidenceTrace_length _) _ ih

def Surface.ProgramIncidenceTrace.Construction.logarithmicSurfaceIncidenceTrace (n m : ℕ) (β : Type) [Fintype β] : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β :=
  (CanonicalCenterIncidenceTrace.Construction.canonicalCenterIncidenceTrace β).appendAtLength (Fintype.card (Finset β)) (CanonicalCenterIncidenceTrace.Construction.canonicalCenterIncidenceTrace_length β)
    (Surface.ProgramIncidenceTrace.Construction.boundedSurfaceIncidenceTrace n m (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels (Fintype.card (Finset β)) β))

theorem Surface.ProgramIncidenceTrace.Construction.logarithmicSurfaceIncidenceTrace_length (n m : ℕ) (β : Type) [Fintype β] :
    (Surface.ProgramIncidenceTrace.Construction.logarithmicSurfaceIncidenceTrace n m β).length = Surface.LogarithmicProgram.Construction.surfaceLogarithmicProgramStepCount n m (Fintype.card β) := by
  classical
  rw [Surface.ProgramIncidenceTrace.Construction.logarithmicSurfaceIncidenceTrace, Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace.appendAtLength_length,
    Surface.ProgramIncidenceTrace.Construction.boundedSurfaceIncidenceTrace_length, Uniform.IncidenceSurfaceLength.Construction.card_iteratedBoundaryLabels, Fintype.card_finset]
  rfl

theorem Surface.LogarithmicProgram.Construction.SurfaceLogarithmicProgram.hasIncidenceTrace
    {n m : ℕ} {β : Type} [Fintype β] {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : Surface.LogarithmicProgram.Construction.SurfaceLogarithmicProgram n m β X f J D Y g K P) :
    P.HasIncidenceTrace β D (Surface.ProgramIncidenceTrace.Construction.logarithmicSurfaceIncidenceTrace n m β) := by
  cases T with
  | component A AM P hcenters hcount hP Q tail =>
      have hhead := A.componentIncidenceCenters_hasTrace _ AM P hcenters
      exact hhead.appendAtLength P Q _ _ _ (CanonicalCenterIncidenceTrace.Construction.canonicalCenterIncidenceTrace_length _) _ tail.hasIncidenceTrace

end

end OAI.AlgebraicGeometry.Resolution.Blowups
