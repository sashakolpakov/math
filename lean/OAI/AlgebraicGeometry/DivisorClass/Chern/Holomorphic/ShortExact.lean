import OAI.AlgebraicGeometry.DivisorClass.Chern.Abelian.SheafLocalExact
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ExponentialEpi
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # Short Exact -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ShortExact

noncomputable section

/-! The short exact exponential sequence of actual holomorphic sheaves. -/

open _root_.CategoryTheory _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (M : Type) [TopologicalSpace M] [ChartedSpace E M]

theorem holomorphicPeriodSheafMap_mono : Mono (PeriodSequence.holomorphicPeriodSheafMap E M) := by
  apply (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mpr
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro U
  exact (AddCommGrpCat.mono_iff_injective _).mpr
    (PeriodSequence.holomorphicPeriodSheafMap_section_injective E M U.unop)

theorem holomorphicExponentialSequence_exact : (PeriodSequence.holomorphicExponentialSequence E M).Exact :=
  Abelian.SheafLocalExact.abelianSheaf_exact_of_section_exact (TopCat.of M) _
    (PeriodSequence.holomorphicExponentialSequence_section_exact E M)

/-- The maps are the actual integral period and pointwise complex exponential. -/
theorem holomorphicExponentialSequence_shortExact :
    (PeriodSequence.holomorphicExponentialSequence E M).ShortExact where
  exact := holomorphicExponentialSequence_exact E M
  mono_f := holomorphicPeriodSheafMap_mono E M
  epi_g := ExponentialEpi.holomorphicExponentialSheafMap_epi E M

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ShortExact
