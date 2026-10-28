import OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultSheafMaps
import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.SheafLocalExact

/-! # Dolbeault Sheaf Zero Exact -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultSheafZeroExact

noncomputable section

/-! The actual holomorphic function sheaf is the degree-zero kernel of the original Dolbeault differential. -/

open _root_.CategoryTheory _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

def holomorphicDolbeaultZeroSequence : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of E)) :=
  ShortComplex.mk (DolbeaultSheafMaps.holomorphicToOpenZeroFormSheaf E) (DolbeaultSheafMaps.openDolbeaultSheafMap E 0)
    (DolbeaultSheafMaps.holomorphicToOpenZeroFormSheaf_d E)

variable [FiniteDimensional ℂ E]

theorem holomorphicDolbeaultZeroSequence_section_exact (U : Opens E) :
    ((holomorphicDolbeaultZeroSequence E).map (Holomorphic.PeriodSequence.abelianSheafSections (TopCat.of E) U)).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro form hform
  change DolbeaultOpen.openDolbeaultD 0 form = 0 at hform
  have h : form ∈ LinearMap.range (DolbeaultZeroKernelMap.holomorphicZeroFormLinear U) := by
    rw [DolbeaultZeroKernelMap.holomorphicZeroFormLinear_range]
    exact hform
  exact h

theorem holomorphicDolbeaultZeroSequence_exact : (holomorphicDolbeaultZeroSequence E).Exact :=
  Abelian.SheafLocalExact.abelianSheaf_exact_of_section_exact (TopCat.of E) _ (holomorphicDolbeaultZeroSequence_section_exact E)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultSheafZeroExact
