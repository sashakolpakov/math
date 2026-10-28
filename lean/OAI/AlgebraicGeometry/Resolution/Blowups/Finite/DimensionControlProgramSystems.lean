import OAI.AlgebraicGeometry.Resolution.Blowups.DimensionControlProgramSystem
import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.ControlProgramSystem

/-! # Dimension Control Program Systems -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DimensionControlProgramSystems.Construction

noncomputable section

/-! The established surface system and the dimension induction step give actual uniform program systems in every finite dimension. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def finiteDimensionControlProgramSystem : (d : ℕ) → Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem (d + 2)
  | 0 => Surface.ControlProgramSystem.Construction.surfaceControlProgramSystem
  | d + 1 => (finiteDimensionControlProgramSystem d).nextDimension

theorem exists_uniform_control_program_system (d : ℕ) :
    ∃ e : ℕ, d ≤ e ∧ Nonempty (Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem e) :=
  ⟨d + 2, Nat.le_add_right d 2, ⟨Construction.finiteDimensionControlProgramSystem d⟩⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Finite.DimensionControlProgramSystems.Construction
