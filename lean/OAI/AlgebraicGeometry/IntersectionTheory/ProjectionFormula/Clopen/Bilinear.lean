import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.PairCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Bilinear

/-! # Bilinear -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Bilinear

noncomputable section

/-! The native finite intersection construction commutes with restriction
to open and closed subpresentations, in all codimensions. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Cycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Supports.ProperCycle OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.PairCycle

variable {V X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (i : V.toOver ⟶ X.toOver)
  [IsOpenImmersion i.left] (m : ℕ)
  [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension m X.structureMap]

theorem restrict_single_image
    (p : ℕ) (A : V.DimensionCycleSupport p) (r : ℚ) :
    CycleMaps.restrict i m p (Finsupp.single (Cycle.supportImage i m p A) r) = Finsupp.single A r := by
  rw [← CycleMaps.embed_single i m, CycleMaps.restrict_embed i m]

theorem restrict_single_outside
    (p : ℕ) (A : X.DimensionCycleSupport p) (r : ℚ) (hA : ¬ (A.val : Set X.carrier) ⊆ Set.range i.left) :
    CycleMaps.restrict i m p (Finsupp.single A r) = 0 := by
  ext D
  rw [CycleMaps.restrict_apply, Finsupp.single_apply, Finsupp.zero_apply]
  apply ite_eq_right
  intro he
  have he' := congrArg Subtype.val he
  apply hA
  rw [he']
  change (ProperCycleLinearity.imageSupport i D.val : Set X.carrier) ⊆ Set.range i.left
  rw [ProperCycleLinearity.imageSupport_eq_image]
  exact Set.image_subset_range _ _

variable [IsClosedImmersion i.left]

theorem pairCycle_restrict (p q : ℕ)
    (A : X.DimensionCycleSupport p) (B : X.DimensionCycleSupport q) :
    CycleMaps.restrict i m (p + q) (Supports.ProperCycle.pairCycle X m p q A B) =
      Supports.ProperCycle.intersectionBilinear V m p q
        (CycleMaps.restrict i m p (Finsupp.single A 1)) (CycleMaps.restrict i m q (Finsupp.single B 1)) := by
  by_cases hA : (A.val : Set X.carrier) ⊆ Set.range i.left
  · by_cases hB : (B.val : Set X.carrier) ⊆ Set.range i.left
    · obtain ⟨A', rfl⟩ : ∃ A', Cycle.supportImage i m p A' = A :=
        ⟨Cycle.supportPreimage i m p A hA, Cycle.supportImage_preimage i m p A hA⟩
      obtain ⟨B', rfl⟩ : ∃ B', Cycle.supportImage i m q B' = B :=
        ⟨Cycle.supportPreimage i m q B hB, Cycle.supportImage_preimage i m q B hB⟩
      rw [PairCycle.pairCycle_restrict_image i m, restrict_single_image i m, restrict_single_image i m]
      simp only [Supports.ProperCycle.intersectionBilinear, Finsupp.linearCombination_single, one_smul]
    · rw [PairCycle.pairCycle_restrict_outside_right i m p q A B hB,
        restrict_single_outside i m q B 1 hB, map_zero]
  · rw [PairCycle.pairCycle_restrict_outside_left i m p q A B hA,
      restrict_single_outside i m p A 1 hA, map_zero, LinearMap.zero_apply]

theorem restrict_bilinear (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) :
    CycleMaps.restrict i m (p + q) (Supports.ProperCycle.intersectionBilinear X m p q a b) =
      Supports.ProperCycle.intersectionBilinear V m p q (CycleMaps.restrict i m p a) (CycleMaps.restrict i m q b) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']
  | single A r =>
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b b' hb hb' => simp only [map_add, hb, hb']
    | single B s =>
      rw [Component.Bilinear.bilinear_single_single, map_smul, map_smul, pairCycle_restrict i m]
      have hr : Finsupp.single A r = r • Finsupp.single A (1 : ℚ) := by simp
      have hs : Finsupp.single B s = s • Finsupp.single B (1 : ℚ) := by simp
      rw [hr, hs, map_smul, map_smul, map_smul, LinearMap.smul_apply, map_smul]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Bilinear
