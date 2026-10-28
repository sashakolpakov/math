import Mathlib.MeasureTheory.Group.Measure

/-! # Multiplicative Measurable Space -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.MultiplicativeMeasurableSpace.Construction

noncomputable section

/-! Measurable structures and translation-invariant measures for an
additive group viewed through the multiplicative type synonym. -/

open _root_.MeasureTheory _root_.MeasureTheory.Measure

instance multiplicativeMeasurableSpace {E : Type*} [MeasurableSpace E] :
    MeasurableSpace (Multiplicative E) := ‹MeasurableSpace E›

instance multiplicativeBorelSpace {E : Type*} [TopologicalSpace E]
    [MeasurableSpace E] [BorelSpace E] : BorelSpace (Multiplicative E) :=
  ‹BorelSpace E›

instance multiplicativeMeasurableMul {E : Type*} [Add E] [MeasurableSpace E] [MeasurableAdd E] :
    MeasurableMul (Multiplicative E) :=
  ⟨fun x => measurable_const_add x.toAdd, fun x => measurable_add_const x.toAdd⟩

theorem additiveHaar_isMulRightInvariant_multiplicative
    {E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E]
    (μ : Measure E) [IsAddRightInvariant μ] :
    IsMulRightInvariant (show Measure (Multiplicative E) from μ) := by
  constructor
  intro x
  exact map_add_right_eq_self μ x.toAdd

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.MultiplicativeMeasurableSpace.Construction
