import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.ResidualFinite
import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.ResidualProgramPullback

/-! # Dimension Control Program System -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The completed residual and coefficient programs construct the uniform program system in the next dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def DimensionControlProgramSystem.Construction.nextDimensionControlProgramSchedule {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d) (b : ℕ) (β : Type) [Fintype β] [DecidableEq β] : Type 1 :=
  Σ m : ℕ, Dimension.ResidualFinite.Construction.DimensionResidualSchedule 𝒮 b m β (fun _ => 0)

def DimensionControlProgramSystem.Construction.nextDimensionControlProgram {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {b : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    (s : DimensionControlProgramSystem.Construction.nextDimensionControlProgramSchedule 𝒮 b β) {X Y : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J : X.IdealSheafData) (D : β → X.IdealSheafData) {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {K : Y.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) : Prop :=
  Dimension.ResidualFinite.Construction.DimensionResidualProgram 𝒮 b s.2 X f J J D Y g K P

def Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem.nextDimension {d : ℕ} (𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d) :
    Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem (d + 1) where
  Schedule := DimensionControlProgramSystem.Construction.nextDimensionControlProgramSchedule 𝒮
  incidenceTrace := fun s => s.2.incidenceTrace
  Program := DimensionControlProgramSystem.Construction.nextDimensionControlProgram
  hasTrace := fun h => h.hasIncidenceTrace
  terminal := by
    intro b hb β _ _ s X Y f _ J D g K P H
    exact H.terminal_order hb
  finitePrograms := by
    intro b hb β ι _ _ _ X _ _ _ f _ J hJ hd D E
    obtain ⟨m, s, hs⟩ := Dimension.ResidualFinite.Construction.exists_finite_dimension_control_programs 𝒮 b hb X f J hJ hd D E
    exact ⟨⟨m, s⟩, hs⟩
  comparison := by
    intro b β _ _ s X Y V W f _ h _ J L D E g k K M P Q H H' q _ hf hJ hD
    exact H.exists_etaleComparison H' q hf hJ hJ hD
  pullback := by
    intro b hb β _ _ s X Y f _ J D g K P H V _ _ _ hd h _ L hL E q _ hf hJ hD
    exact H.exists_etale_pullback hb V hd h L L hL hL E q hf hJ hJ hD

end

end OAI.AlgebraicGeometry.Resolution.Blowups
