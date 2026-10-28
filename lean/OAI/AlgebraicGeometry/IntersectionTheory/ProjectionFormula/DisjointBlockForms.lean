import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BlockSupports
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CoordinateBlockForms
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projection.Generic

/-! # Disjoint Block Forms -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DisjointBlockForms

noncomputable section

/-! One generic projection on the disjoint blocks is defined on
the whole source and base, has independent restrictions to both blocks,
and satisfies all the required source/base incidence bounds. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

namespace Projection

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Projective.BlockSupports

theorem exists_forms (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) [IsIntegral X.carrier]
    (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]
    (S : IrreducibleCloseds (Projective.Dimension.SpacePresentation.presentation m).carrier)
    {τ : Type} [Finite τ] (Z : τ → IrreducibleCloseds X.carrier) :
    ∃ L : Fin (m + 1) → Foundations.Scheme.ProjectiveSpace.projectiveGrading (X.ambientDimension + m + 1) 1,
      (∀ x : X.carrier, ∃ a, (L a).val ∉ ((Projective.BlockSupports.source X m).left x).asHomogeneousIdeal) ∧
      (∀ y : (Projective.Dimension.SpacePresentation.presentation m).carrier,
        ∃ a, (L a).val ∉ ((Projective.BlockSupports.target X m).left y).asHomogeneousIdeal) ∧
      LinearIndependent ℂ (fun a => CoordinateBlockForms.restrict (DisjointProjectiveBlocks.leftIndex X.ambientDimension m) (L a)) ∧
      LinearIndependent ℂ (fun a => CoordinateBlockForms.restrict (DisjointProjectiveBlocks.rightIndex X.ambientDimension m) (L a)) ∧
      ∀ t, Projection.Generic.InductionBounds.incidence (Projective.BlockSupports.ambient X m)
        (ProperCycleLinearity.imageSupport (Projective.BlockSupports.target X m) S) (ProperCycleLinearity.imageSupport (Projective.BlockSupports.source X m) (Z t)) L := by
  have hm := EmbeddedFundamentalSupport.dimension_le X m
  let e : Foundations.Scheme.ProjectiveSpace.projectiveGrading m 1 ≃ₗ[ℂ] (Fin (m + 1) → ℂ) :=
    LinearEquiv.ofFinrankEq _ _ (by rw [LinearFormBasis.dimension, Module.finrank_fin_fun])
  let j := Fin.castLE (Nat.add_le_add_right hm 1)
  let Q := e.toLinearMap.comp (CoordinateBlockForms.restrict j)
  have hQ : Function.Surjective Q := e.surjective.comp
    (CoordinateBlockForms.surjective j (Fin.castLE_injective _))
  let F := CoordinateBlockForms.restrict (DisjointProjectiveBlocks.leftIndex X.ambientDimension m)
  let G := CoordinateBlockForms.restrict (DisjointProjectiveBlocks.rightIndex X.ambientDimension m)
  let D : Bool → Foundations.Scheme.ProjectiveSpace.projectiveGrading (X.ambientDimension + m + 1) 1 →ₗ[ℂ] (Fin (m + 1) → ℂ) :=
    fun b => if b then e.toLinearMap.comp G else Q.comp F
  have hD : ∀ b, Function.Surjective (D b) := by
    intro b
    cases b
    · exact hQ.comp (CoordinateBlockForms.surjective _ (DisjointProjectiveBlocks.left_injective _ _))
    · exact e.surjective.comp (CoordinateBlockForms.surjective _ (DisjointProjectiveBlocks.right_injective _ _))
  let H : Bool → IrreducibleCloseds (Projective.BlockSupports.ambient X m).carrier := fun b => if b then Projective.BlockSupports.targetWhole X m else Projective.BlockSupports.sourceWhole X m
  have hH : ∀ b, Foundations.Scheme.SupportDimension.supportTranscendenceDimension (H b) (Projective.BlockSupports.ambient X m).structureMap ≤ m := by
    intro b
    cases b
    · exact (Projective.BlockSupports.sourceWhole_dimension X m m).le
    · exact (Projective.BlockSupports.targetWhole_dimension X m).le
  obtain ⟨L, _, _, hI, hbase, hLI⟩ := Projection.Generic.OnSupports.exists_forms (Projective.BlockSupports.ambient X m) m
    (fun _ : τ => ProperCycleLinearity.imageSupport (Projective.BlockSupports.target X m) S) (fun t => ProperCycleLinearity.imageSupport (Projective.BlockSupports.source X m) (Z t)) D hD H hH
  refine ⟨L, ?_, ?_, LinearIndependent.of_comp Q (hLI false),
    LinearIndependent.of_comp e.toLinearMap (hLI true), hI⟩
  · intro x
    have hx : (Projective.BlockSupports.source X m).left x ∈ (H false : Set (Projective.BlockSupports.ambient X m).carrier) := by
      change (Projective.BlockSupports.source X m).left x ∈ (ProperCycleLinearity.imageSupport (Projective.BlockSupports.source X m) (Integral.Fundamental.whole X) : Set (Projective.BlockSupports.ambient X m).carrier)
      rw [ProperCycleLinearity.imageSupport_eq_image]
      exact ⟨x, trivial, rfl⟩
    exact hbase false _ hx
  · intro y
    have hy : (Projective.BlockSupports.target X m).left y ∈ (H true : Set (Projective.BlockSupports.ambient X m).carrier) := by
      change (Projective.BlockSupports.target X m).left y ∈ (ProperCycleLinearity.imageSupport (Projective.BlockSupports.target X m)
        (Integral.Fundamental.whole (Projective.Dimension.SpacePresentation.presentation m)) : Set (Projective.BlockSupports.ambient X m).carrier)
      rw [ProperCycleLinearity.imageSupport_eq_image]
      exact ⟨y, trivial, rfl⟩
    exact hbase true _ hy

end Projection

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.DisjointBlockForms
