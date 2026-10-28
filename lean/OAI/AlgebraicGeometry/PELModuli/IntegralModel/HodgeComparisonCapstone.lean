import OAI.AlgebraicGeometry.Albanese.HodgeComparisonIs
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.AlbaneseCohomology

/-! # Hodge Comparison Capstone -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.HodgeComparisonCapstone

/-! Use the proved native HodgeComparison comparison with the identical IntegralModel input
proposition. The adapter preserves the actual Albanese pullback map. -/

theorem provedHodgeComparisonInput : AlbaneseCohomology.HodgeComparisonInput := by
  intro X x₀ A a ha
  exact Albanese.HodgeComparisonIs.CM.Construction.albanese_h1_hodge_iso X x₀ A a ha

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.HodgeComparisonCapstone
