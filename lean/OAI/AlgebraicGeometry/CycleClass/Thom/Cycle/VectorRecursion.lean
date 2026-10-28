import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorPresentationTarget
import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.VectorStep
import OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionStepIsolation

/-! # Vector Recursion -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorRecursion.Constructions

noncomputable section

/-! Intrinsic recursion for the actual cycle-vector class: the
principal step and remaining vector give the same class after the
literal equality of their intersection supports. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Vector.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorPresentationTarget.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.SectionSupport OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVector.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Finite.VectorStep.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Finite.SectionEuler.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity.Constructions.SupportedCupTargets OAI.AlgebraicGeometry.CycleClass.Thom.ThomOpenRestriction.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.AmbientMap.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Affine.SectionFunction.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable (p n : ℕ) (B : V.carrier.Opens) [Nonempty B]
  (r : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
  (U : Opens V.analyticSpace)
  (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
  {L : Type} (u : L → U) (hu : IsOpen (Set.range u)ᶜ)

local notation "j" => OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B
local notation "w" => OAI.AlgebraicGeometry.CycleClass.Thom.NormalizationAffine.SectionSupport.Constructions.baseSectionImage j U hU r
local notation "v" => OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage j U hU n s
local notation "hv" => OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage_openComplement j U hU n s
local notation "ht" => OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage_mapsTo j U hU n s
local notation "S" => Set.range u ∩ Set.range w
local notation "G" => Set.range w ∩ Set.range v
local notation "F" => (Set.range u ∩ Set.range w) ∩ Set.range v
local notation "u₁" => (Subtype.val : {y : U // y ∈ Set.range u ∩ Set.range w} → U)

include hu in
theorem cutImage_openComplement : IsOpen (Set.range u₁)ᶜ := by
  rw [Subtype.range_coe]
  exact Finite.VectorStep.Constructions.step_openComplement V B r U hU u hu

theorem headTailIntersection_eq :
    Vector.Constructions.Class.vectorIntersectionSupport V B U hU u (n + 1) (Fin.cons r s) =
      Vector.Constructions.Class.vectorIntersectionSupport V B U hU u₁ n s := by
  change Set.range u ∩ Set.range (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage j U hU (n + 1) (Fin.cons r s)) =
    Set.range u₁ ∩ Set.range v
  rw [BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage_cons, Subtype.range_coe, Set.inter_assoc]

theorem tailClass_mapsTo : Set.MapsTo (𝟙 (TopCat.of U))
    (Vector.Constructions.Class.vectorIntersectionSupport V B U hU u (n + 1) (Fin.cons r s))ᶜ
    (Vector.Constructions.Class.vectorIntersectionSupport V B U hU u₁ n s)ᶜ :=
  EvenIntersectionAssociativity.Constructions.SupportedCupTargets.id_mapsTo_eq _ _ _ (congrArg Set.compl (headTailIntersection_eq V n B r s U hU u))

variable (c : Geometric.DimensionCycles.RationalDimensionCycle V p)
  (hc : ∀ D : Geometric.DimensionCycles.DimensionCycleSupport V p, c D ≠ 0 →
    (Subtype.val : U → V.analyticSpace) ⁻¹' Set.range D.analyticInclusion ⊆ Set.range u)
  (hne : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p), c D ≠ 0 → Nonempty ((Normalization.AmbientMap.Constructions.normalizationToAmbient V D.val).left ⁻¹ᵁ B))
  (hr : ∀ (D : Geometric.DimensionCycles.DimensionCycleSupport V p) (hD : c D ≠ 0), letI := hne D hD
    Affine.SectionFunction.Constructions.parentSectionFunction D B r ≠ 0)

include hc in
theorem cycleVectorClassAt_step :
    Vector.Constructions.Class.cycleVectorClassAt V B U hU u p (n + 1) ((p + 1) + n) (by omega) (Fin.cons r s) hu c =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
        (tailClass_mapsTo V n B r s U hU u) (2 * ((p + 1) + n))
        (Vector.Constructions.Class.cycleVectorClassAt V B U hU u₁ (p + 1) n ((p + 1) + n) rfl s
          (cutImage_openComplement V B r U hU u hu) (Finite.SectionEuler.Constructions.originalPrincipalStepSum V p B r c hne hr)) := by
  let d := (p + 1) + n
  have hT : Set.range (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage j U hU (n + 1) (Fin.cons r s)) = G := BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage_cons j U hU n r s
  have hF : Set.range u ∩ G = F := (Set.inter_assoc (Set.range u) (Set.range w) (Set.range v)).symm
  let hf := VectorPresentationTarget.Constructions.presentTo_mapsTo V B U hU u (n + 1) (Fin.cons r s) (Set.range u) G F rfl hT hF
  let hg := VectorPresentationTarget.Constructions.presentTo_mapsTo V B U hU u₁ n s S (Set.range v) F Subtype.range_coe rfl rfl
  apply VectorPresentationTarget.Constructions.presentTo_injective V B U hU u (n + 1) (Fin.cons r s) (Set.range u) G F rfl hT hF (2 * d)
  have hleft := VectorPresentationTarget.Constructions.presentTo_cycleVectorClass V B U hU u (n + 1) (Fin.cons r s)
    (Set.range u) G F rfl hT hF p d (by omega) hu hu (Finite.VectorStep.Constructions.vector_openComplement V B r U hU v hv)
    (Finite.VectorStep.Constructions.finalComplement_eq V B r U hU u v) (Finite.VectorStep.Constructions.vector_mapsTo V n B r s U hU v ht) c
  have hraw := Finite.VectorStep.Constructions.cycle_vectorCup_eq_step_vectorCup V p n B r s U hU u hu v hv ht c hc hne hr
  rw [Finite.SectionEuler.Constructions.cycleSectionStep_eq_sum] at hraw
  let z := Vector.Constructions.Class.cycleVectorClassAt V B U hU u₁ (p + 1) n d rfl s (cutImage_openComplement V B r U hU u hu)
    (Finite.SectionEuler.Constructions.originalPrincipalStepSum V p B r c hne hr)
  have hcomp := ConcreteCategory.congr_hom
    (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_comp (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U)) (𝟙 (TopCat.of U))
      hf (tailClass_mapsTo V n B r s U hU u) (2 * d)) z
  have hright := VectorPresentationTarget.Constructions.presentTo_cycleVectorClass V B U hU u₁ n s S (Set.range v) F Subtype.range_coe rfl rfl
    (p + 1) d rfl (cutImage_openComplement V B r U hU u hu) (Finite.VectorStep.Constructions.step_openComplement V B r U hU u hu) hv
    (Finite.VectorStep.Constructions.stepComplement_eq V B r U hU u v) ht (Finite.SectionEuler.Constructions.originalPrincipalStepSum V p B r c hne hr)
  have he : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U)) hf (2 * d)
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
        (tailClass_mapsTo V n B r s U hU u) (2 * d) z) =
      AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U)) hg (2 * d) z := hcomp
  exact hleft.trans (hraw.trans (he.trans hright).symm)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorRecursion.Constructions
