import OAI.AlgebraicGeometry.Albanese.Construction.Mon
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Albanese

/-! # Construction Capstone -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConstructionCapstone

/-! The proved Construction capstone supplies the exact native pointed Albanese
existence proposition used by IntegralModel. -/

theorem provedConstructionInput : Albanese.ConstructionInput := by
  intro X hX x₀
  exact Albanese.Construction.Mon.exists_albanese X x₀

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.ConstructionCapstone
