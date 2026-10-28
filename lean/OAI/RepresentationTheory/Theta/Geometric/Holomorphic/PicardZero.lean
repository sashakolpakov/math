import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting

/-! # Picard Zero -/

namespace OAI.RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero

noncomputable section

/-! The zero-Chern part of the actual holomorphic Picard cohomology
is the image of first cohomology of the holomorphic function sheaf. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.CategoryTheory.Abelian _root_.TopologicalSpace

open OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (M : Type) [TopologicalSpace M] [ChartedSpace E M]

def holomorphicExponentialH1 :
    CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1 →+ AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology E M :=
  CategoryTheory.Sheaf.H.map (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicExponentialSheafMap E M) 1

theorem holomorphicExponentialH1_connecting
    (v : CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1) :
    AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting E M (holomorphicExponentialH1 E M v) = 0 := by
  change (v.comp (Ext.mk₀ (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.PeriodSequence.holomorphicExponentialSequence E M).g) (add_zero 1)).comp
    (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ShortExact.holomorphicExponentialSequence_shortExact E M).extClass (rfl : 1 + 1 = 2) = 0
  simp only [Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

theorem exists_holomorphicH1_of_connecting_zero (u : AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting.holomorphicUnitCohomology E M)
    (hu : AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting E M u = 0) :
    ∃ v : CategoryTheory.Sheaf.H (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Sheaves.holomorphicFunctionSheaf E M) 1, holomorphicExponentialH1 E M v = u :=
  Ext.covariant_sequence_exact₃ _ (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.ShortExact.holomorphicExponentialSequence_shortExact E M) u
    (rfl : 1 + 1 = 2) hu

theorem holomorphicExponentialH1_range :
    (holomorphicExponentialH1 E M).range = (AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Connecting.holomorphicExponentialConnecting E M).ker := by
  ext u
  constructor
  · rintro ⟨v, rfl⟩
    exact holomorphicExponentialH1_connecting E M v
  · exact exists_holomorphicH1_of_connecting_zero E M u

end

end OAI.RepresentationTheory.Theta.Geometric.Holomorphic.PicardZero
