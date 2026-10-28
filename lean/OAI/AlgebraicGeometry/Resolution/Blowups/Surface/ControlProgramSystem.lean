import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.ControlProgramSystem

/-! # Control Program System -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface.ControlProgramSystem.Construction

noncomputable section

/-! The established surface programs supply the complete uniform program interface in dimension two. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def surfaceControlProgramSchedule (b : ℕ) (β : Type) [Fintype β] [DecidableEq β] : Type 1 :=
  Σ m : ℕ, ResidualSchedule.Construction.SurfaceResidualSchedule b m β (fun _ => 0)

def surfaceControlProgram {b : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    (s : surfaceControlProgramSchedule b β) {X Y : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J : X.IdealSheafData) (D : β → X.IdealSheafData) {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) : Prop :=
  ResidualProgram.Construction.SurfaceResidualProgram b s.2 X f J J D Y g K P

def surfaceControlProgramSystem : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem 2 where
  Schedule := surfaceControlProgramSchedule
  incidenceTrace := fun s => s.2.incidenceTrace
  Program := surfaceControlProgram
  hasTrace := fun h => h.hasIncidenceTrace
  terminal := by
    intro b hb β _ _ s X Y f _ J D g K P H
    exact H.terminal_order hb
  finitePrograms := by
    intro b hb β ι _ _ _ X _ _ _ f _ J hJ hd D E
    obtain ⟨m, s, hs⟩ := ControlFinitePrograms.Construction.exists_finite_surface_control_programs b hb X f J hJ hd D E
    exact ⟨⟨m, s⟩, hs⟩
  comparison := by
    intro b β _ _ s X Y V W f _ h _ J L D E g k K M P Q H H' q _ hf hJ hD
    exact H.exists_etaleComparison H' q hf hJ hJ hD
  pullback := by
    intro b hb β _ _ s X Y f _ J D g K P H V _ _ _ hd h _ L hL E q _ hf hJ hD
    exact H.exists_etale_pullback hb V hd h L L hL hL E q hf hJ hJ hD

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface.ControlProgramSystem.Construction
