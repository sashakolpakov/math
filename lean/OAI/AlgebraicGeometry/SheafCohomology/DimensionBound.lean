import OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimensionDrop
import Mathlib.Topology.KrullDimension

/-! # Dimension Bound -/

namespace OAI.AlgebraicGeometry.SheafCohomology.DimensionBound.Projective

noncomputable section

/-! Bounding Zariski Krull dimension by the actual function-field transcendence degree. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

/-- Every strict chain of irreducible closed supports gives a strict chain of
their nonnegative transcendence dimensions. -/
theorem supportHeight_le_transcendenceDimension
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] (Z : IrreducibleCloseds X) :
    Order.height Z ≤ (Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z f : ℕ∞) := by
  simpa only [Order.height_nat] using
    Order.height_le_height_apply_of_strictMono
      (fun W : IrreducibleCloseds X => Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f)
      (Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono f) Z

/-- On an integral scheme locally of finite type over a field, the topological
Krull dimension is bounded by the genuine scheme transcendence dimension. -/
theorem topologicalKrullDim_le_schemeTranscendenceDimension
    {K : Type u} [Field K] {X : Scheme.{u}} [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    topologicalKrullDim X ≤ (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f : WithBot ℕ∞) := by
  rw [topologicalKrullDim, Order.krullDim_eq_iSup_height]
  refine iSup_le fun Z => ?_
  apply WithBot.coe_le_coe.mpr
  refine (supportHeight_le_transcendenceDimension f Z).trans ?_
  exact_mod_cast Foundations.Scheme.SupportDimension.supportTranscendenceDimension_le Z f

end

end OAI.AlgebraicGeometry.SheafCohomology.DimensionBound.Projective
