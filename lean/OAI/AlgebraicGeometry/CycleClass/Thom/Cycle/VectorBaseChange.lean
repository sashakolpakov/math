import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Vector
import OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal
import OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction

/-! # Vector Base Change -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorBaseChange.Constructions

noncomputable section

/-! The actual finite-cycle vector class is preserved when its
algebraic base and all its regular sections are restricted. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Vector.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.Change OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.SectionSupport
open OAI.AlgebraicGeometry.CycleClass.Thom.Supported.CupNaturality.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Normal OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions.HeadDifference
open OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable (B C : V.carrier.Opens) (hCB : C ≤ B) [Nonempty B] [Nonempty C] (U : Opens V.analyticSpace)
  (hUB : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
  (hUC : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C)))
  {L : Type} (u : L → U) (n : ℕ) (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))

local notation "k" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions.openRestriction V.toOver hCB
local notation "hk" => OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.SectionEvaluation.Constructions.openRestriction_inclusion V.toOver hCB
local notation "sC" => (fun i => OAI.AlgebraicGeometry.CycleClass.Thom.Section.BaseRestriction.Constructions.HeadDifference.restrictSection V B C hCB (s i))

theorem baseChangeIntersection_mapsTo : Set.MapsTo (𝟙 (TopCat.of U))
    (Vector.Constructions.Class.vectorIntersectionSupport V C U hUC u n sC)ᶜ (Vector.Constructions.Class.vectorIntersectionSupport V B U hUB u n s)ᶜ := by
  intro x hx hy
  exact hx ⟨hy.1, (BaseVectorNormal.Constructions.Change.vectorZeroImage_change (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C) k hk U hUB hUC n s).symm ▸ hy.2⟩

theorem cycleVectorClassAt_base_change (p d : ℕ) (hd : p + n = d) (hu : IsOpen (Set.range u)ᶜ)
    (c : Geometric.DimensionCycles.RationalDimensionCycle V p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (baseChangeIntersection_mapsTo V B C hCB U hUB hUC u n s) (2 * d)
      (Vector.Constructions.Class.cycleVectorClassAt V B U hUB u p n d hd s hu c) =
    Vector.Constructions.Class.cycleVectorClassAt V C U hUC u p n d hd sC hu c := by
  let old := BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hUB n s
  let new := BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C) U hUC n sC
  let hf : Set.MapsTo (𝟙 (TopCat.of U)) (Set.range u)ᶜ (Set.range u)ᶜ := fun _ hx => hx
  have h := Supported.CupNaturality.Constructions.cupTo_naturality (𝟙 (TopCat.of U)) (Set.range u)ᶜ (Set.range new)ᶜ
    (Vector.Constructions.Class.vectorIntersectionSupport V C U hUC u n sC)ᶜ
    (Set.range u)ᶜ (Set.range old)ᶜ (Vector.Constructions.Class.vectorIntersectionSupport V B U hUB u n s)ᶜ
    hu (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C) U hUC n sC)
    hu (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hUB n s)
    (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq u new) (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq u old) hf
    (BaseVectorNormal.Constructions.Change.vectorChange_mapsTo (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C) k hk U hUB hUC n s)
    (baseChangeIntersection_mapsTo V B C hCB U hUB hUC u n s)
    (2 * p) (2 * n) (2 * d) (by omega)
    (Open.SupportedLift.Constructions.Map.relativeClassMap V U (Set.range u) p (Open.SupportedLift.Constructions.restrictCycle V U (Set.range u) p c))
    (BaseVectorNormal.Constructions.Class.vectorNormalClass (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hUB n s)
  have hparent : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U)) hf (2 * p)
      (Open.SupportedLift.Constructions.Map.relativeClassMap V U (Set.range u) p (Open.SupportedLift.Constructions.restrictCycle V U (Set.range u) p c)) =
      Open.SupportedLift.Constructions.Map.relativeClassMap V U (Set.range u) p (Open.SupportedLift.Constructions.restrictCycle V U (Set.range u) p c) :=
    ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id (ModuleCat.of ℚ ℚ) (TopCat.of U) (Set.range u)ᶜ (2 * p)) _
  have hvector := BaseVectorNormal.Constructions.Change.vectorNormalClass_change (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C) k hk U hUB hUC n s
  exact h.symm.trans (congrArg₂
    (fun (aa : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) (Set.range u)ᶜ (2 * p))
      (bb : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U) (Set.range new)ᶜ (2 * n)) =>
      EvenIntersectionAssociativity.Constructions.SupportedCupTargets.cupTo (TopCat.of U) (Set.range u)ᶜ (Set.range new)ᶜ
        (Vector.Constructions.Class.vectorIntersectionSupport V C U hUC u n sC)ᶜ hu
        (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion C) U hUC n sC) (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq u new)
        (2 * p) (2 * n) (2 * d) (by omega) aa bb) hparent hvector)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorBaseChange.Constructions
