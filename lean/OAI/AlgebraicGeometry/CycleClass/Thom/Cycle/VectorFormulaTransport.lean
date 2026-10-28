import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorBaseChange
import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorRecursion
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportTransport

/-! # Vector Formula Transport -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorFormulaTransport.Constructions

noncomputable section

/-! Transport of an actual finite-cycle formula under base restriction,
elementary head changes, and the intrinsic principal-section recurrence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Vector.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorBaseChange.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorRecursion.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.Change OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.SectionSupport OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportTransport.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions.HeadDifference OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionEuler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem identityMap_injective (X : TopCat.{0}) {A B : Set X} (h : A = B)
    (hm : Set.MapsTo (𝟙 X) B A) (d : ℕ) :
    Function.Injective (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 X) hm d) := by
  subst B
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id]
  exact Function.injective_id

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable (B C : V.carrier.Opens) (hCB : C ≤ B) [Nonempty B] [Nonempty C]
  (U : Opens V.analyticSpace)
  (hUB : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
  (hUC : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C)))
  {L : Type} (u : L → U) (p n d : ℕ)
  (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (hu : IsOpen (Set.range u)ᶜ)
  (c : Geometric.DimensionCycles.RationalDimensionCycle V p) (z : Geometric.DimensionCycles.RationalDimensionCycle V d)

theorem formula_of_base_change (hd : p + n = d)
    (h : Vector.Constructions.Class.cycleVectorClassAt V C U hUC u p n d hd (fun i => Section.BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (s i)) hu c =
      Open.SupportedLift.Constructions.Map.relativeClassMap V U (Vector.Constructions.Class.vectorIntersectionSupport V C U hUC u n (fun i => Section.BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (s i))) d
        (Open.SupportedLift.Constructions.restrictCycle V U (Vector.Constructions.Class.vectorIntersectionSupport V C U hUC u n (fun i => Section.BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (s i))) d z)) :
    Vector.Constructions.Class.cycleVectorClassAt V B U hUB u p n d hd s hu c =
      Open.SupportedLift.Constructions.Map.relativeClassMap V U (Vector.Constructions.Class.vectorIntersectionSupport V B U hUB u n s) d
        (Open.SupportedLift.Constructions.restrictCycle V U (Vector.Constructions.Class.vectorIntersectionSupport V B U hUB u n s) d z) := by
  have he : Vector.Constructions.Class.vectorIntersectionSupport V B U hUB u n s =
      Vector.Constructions.Class.vectorIntersectionSupport V C U hUC u n (fun i => Section.BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (s i)) := by
    exact congrArg (fun S => Set.range u ∩ S)
      (BaseVectorNormal.Constructions.Change.vectorZeroImage_change (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C) (Scheme.SectionEvaluation.Constructions.openRestriction V.toOver hCB)
        (Scheme.SectionEvaluation.Constructions.openRestriction_inclusion V.toOver hCB) U hUB hUC n s).symm
  apply identityMap_injective (TopCat.of U) (congrArg Set.compl he)
    (VectorBaseChange.Constructions.baseChangeIntersection_mapsTo V B C hCB U hUB hUC u n s) (2 * d)
  exact (VectorBaseChange.Constructions.cycleVectorClassAt_base_change V B C hCB U hUB hUC u n s p d hd hu c).trans
    (h.trans (Open.SupportTransport.Constructions.relativeClassMap_restrict_support_congr V U _ _ he d z).symm)

omit [Nonempty C] in
theorem formula_of_head_change (r : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
    (a : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (ha : a ∈ Ideal.span (Set.range s))
    (hd : p + (n + 1) = d)
    (h : Vector.Constructions.Class.cycleVectorClassAt V B U hUB u p (n + 1) d hd (Fin.cons (r + a) s) hu c =
      Open.SupportedLift.Constructions.Map.relativeClassMap V U (Vector.Constructions.Class.vectorIntersectionSupport V B U hUB u (n + 1) (Fin.cons (r + a) s)) d
        (Open.SupportedLift.Constructions.restrictCycle V U (Vector.Constructions.Class.vectorIntersectionSupport V B U hUB u (n + 1) (Fin.cons (r + a) s)) d z)) :
    Vector.Constructions.Class.cycleVectorClassAt V B U hUB u p (n + 1) d hd (Fin.cons r s) hu c =
      Open.SupportedLift.Constructions.Map.relativeClassMap V U (Vector.Constructions.Class.vectorIntersectionSupport V B U hUB u (n + 1) (Fin.cons r s)) d
        (Open.SupportedLift.Constructions.restrictCycle V U (Vector.Constructions.Class.vectorIntersectionSupport V B U hUB u (n + 1) (Fin.cons r s)) d z) := by
  have he : Vector.Constructions.Class.vectorIntersectionSupport V B U hUB u (n + 1) (Fin.cons r s) =
      Vector.Constructions.Class.vectorIntersectionSupport V B U hUB u (n + 1) (Fin.cons (r + a) s) :=
    congrArg (fun S => Set.range u ∩ S) (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage_head_change (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hUB n r s a ha).symm
  apply identityMap_injective (TopCat.of U) (congrArg Set.compl he)
    (Vector.Constructions.Class.headChangeIntersection_mapsTo V B U hUB u n r s a ha) (2 * d)
  exact (Vector.Constructions.Class.cycleVectorClassAt_head_change V B U hUB u n r s a ha p d hd hu c).trans
    (h.trans (Open.SupportTransport.Constructions.relativeClassMap_restrict_support_congr V U _ _ he d z).symm)

omit [Nonempty C] in
theorem formula_of_step (r : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (hd : p + (n + 1) = d)
    (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 →
      (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ Set.range u)
    (hne : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 → Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B))
    (hr : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0), letI := hne D hD
      Affine.SectionFunction.Constructions.parentSectionFunction D B r ≠ 0)
    (h : Vector.Constructions.Class.cycleVectorClassAt V B U hUB
      (Subtype.val : {y : U // y ∈ Set.range u ∩ Set.range (NormalizationAffine.SectionSupport.Constructions.baseSectionImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hUB r)} → U)
      (p + 1) n d (by omega) s (VectorRecursion.Constructions.cutImage_openComplement V B r U hUB u hu)
      (Finite.SectionEuler.Constructions.originalPrincipalStepSum V p B r c hne hr) =
      Open.SupportedLift.Constructions.Map.relativeClassMap V U (Vector.Constructions.Class.vectorIntersectionSupport V B U hUB
        (Subtype.val : {y : U // y ∈ Set.range u ∩ Set.range (NormalizationAffine.SectionSupport.Constructions.baseSectionImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hUB r)} → U) n s) d
        (Open.SupportedLift.Constructions.restrictCycle V U (Vector.Constructions.Class.vectorIntersectionSupport V B U hUB
          (Subtype.val : {y : U // y ∈ Set.range u ∩ Set.range (NormalizationAffine.SectionSupport.Constructions.baseSectionImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hUB r)} → U) n s) d z)) :
    Vector.Constructions.Class.cycleVectorClassAt V B U hUB u p (n + 1) d hd (Fin.cons r s) hu c =
      Open.SupportedLift.Constructions.Map.relativeClassMap V U (Vector.Constructions.Class.vectorIntersectionSupport V B U hUB u (n + 1) (Fin.cons r s)) d
        (Open.SupportedLift.Constructions.restrictCycle V U (Vector.Constructions.Class.vectorIntersectionSupport V B U hUB u (n + 1) (Fin.cons r s)) d z) := by
  have he : (p + 1) + n = d := by omega
  cases he
  have hstep := VectorRecursion.Constructions.cycleVectorClassAt_step V p n B r s U hUB u hu c hc hne hr
  rw [h] at hstep
  exact hstep.trans (Open.SupportTransport.Constructions.relativeClassMap_restrict_support_congr V U _ _
    (VectorRecursion.Constructions.headTailIntersection_eq V n B r s U hUB u).symm ((p + 1) + n) z)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorFormulaTransport.Constructions
