import OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal
import OAI.AlgebraicGeometry.CycleClass.Thom.Supported.CupNaturality
import OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift

/-! # Vector -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Vector.Constructions.Class

noncomputable section

/-! The actual finite cycle cup with a section-vector normal class,
in a specified cycle grading and its literal common zero support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.SectionSupport OAI.AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity.Constructions.SupportedCupTargets OAI.AlgebraicGeometry.CycleClass.Thom.Supported.CupNaturality.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionTo.Constructions.Normal OAI.AlgebraicGeometry.CycleClass.Thom.ImageIntersectionCup.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable (B : V.carrier.Opens) [Nonempty B] (U : Opens V.analyticSpace)
  (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
  {L : Type} (u : L → U)

def vectorIntersectionSupport (n : ℕ) (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) : Set U :=
  Set.range u ∩ Set.range (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU n s)

def cycleVectorClassAt (p n d : ℕ) (hd : p + n = d) (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
    (hu : IsOpen (Set.range u)ᶜ) (c : Geometric.DimensionCycles.RationalDimensionCycle V p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology (ModuleCat.of ℚ ℚ) (TopCat.of U)
      (vectorIntersectionSupport V B U hU u n s)ᶜ (2 * d) :=
  EvenIntersectionAssociativity.Constructions.SupportedCupTargets.cupTo (TopCat.of U) (Set.range u)ᶜ (Set.range (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU n s))ᶜ
    (vectorIntersectionSupport V B U hU u n s)ᶜ hu (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU n s)
    (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq u (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU n s))
    (2 * p) (2 * n) (2 * d) ((Nat.mul_add 2 p n).symm.trans (congrArg (fun k => 2 * k) hd))
    (Open.SupportedLift.Constructions.Map.relativeClassMap V U (Set.range u) p (Open.SupportedLift.Constructions.restrictCycle V U (Set.range u) p c))
    (BaseVectorNormal.Constructions.Class.vectorNormalClass (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU n s)

theorem cycleVectorClassAt_eq_imageCup (p n : ℕ) (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
    (hu : IsOpen (Set.range u)ᶜ) (c : Geometric.DimensionCycles.RationalDimensionCycle V p) :
    cycleVectorClassAt V B U hU u p n (p + n) rfl s hu c =
      ImageIntersectionCup.Constructions.imageIntersectionCup u (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU n s) hu
        (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU n s) p n
        (Open.SupportedLift.Constructions.Map.relativeClassMap V U (Set.range u) p (Open.SupportedLift.Constructions.restrictCycle V U (Set.range u) p c))
        (BaseVectorNormal.Constructions.Class.vectorNormalClass (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU n s) :=
  (EvenIntersectionAssociativity.Constructions.SupportedCupTargets.imageIntersectionCup_eq_cupTo u (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU n s) hu
    (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU n s) p n _ _).symm

variable (n : ℕ) (r : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
  (a : Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤)) (ha : a ∈ Ideal.span (Set.range s))

include ha in
theorem headChangeIntersection_mapsTo : Set.MapsTo (𝟙 (TopCat.of U))
    (vectorIntersectionSupport V B U hU u (n + 1) (Fin.cons (r + a) s))ᶜ
    (vectorIntersectionSupport V B U hU u (n + 1) (Fin.cons r s))ᶜ := by
  intro x hx hy
  exact hx ⟨hy.1, (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage_head_change (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU n r s a ha).symm ▸ hy.2⟩

theorem cycleVectorClassAt_head_change (p d : ℕ) (hd : p + (n + 1) = d)
    (hu : IsOpen (Set.range u)ᶜ) (c : Geometric.DimensionCycles.RationalDimensionCycle V p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (headChangeIntersection_mapsTo V B U hU u n r s a ha) (2 * d)
      (cycleVectorClassAt V B U hU u p (n + 1) d hd (Fin.cons r s) hu c) =
    cycleVectorClassAt V B U hU u p (n + 1) d hd (Fin.cons (r + a) s) hu c := by
  let old := BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU (n + 1) (Fin.cons r s)
  let new := BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU (n + 1) (Fin.cons (r + a) s)
  let hf : Set.MapsTo (𝟙 (TopCat.of U)) (Set.range u)ᶜ (Set.range u)ᶜ := fun _ hx => hx
  have h := Supported.CupNaturality.Constructions.cupTo_naturality (𝟙 (TopCat.of U)) (Set.range u)ᶜ (Set.range new)ᶜ
    (vectorIntersectionSupport V B U hU u (n + 1) (Fin.cons (r + a) s))ᶜ
    (Set.range u)ᶜ (Set.range old)ᶜ (vectorIntersectionSupport V B U hU u (n + 1) (Fin.cons r s))ᶜ
    hu (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU (n + 1) (Fin.cons (r + a) s))
    hu (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage_openComplement (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU (n + 1) (Fin.cons r s))
    (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq u new) (ImageIntersectionTo.Constructions.Normal.intersectionComplement_eq u old) hf
    (BaseVectorNormal.Constructions.Class.headChange_mapsTo (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU n r s a ha)
    (headChangeIntersection_mapsTo V B U hU u n r s a ha)
    (2 * p) (2 * (n + 1)) (2 * d) (by omega)
    (Open.SupportedLift.Constructions.Map.relativeClassMap V U (Set.range u) p (Open.SupportedLift.Constructions.restrictCycle V U (Set.range u) p c))
    (BaseVectorNormal.Constructions.Class.vectorNormalClass (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU (n + 1) (Fin.cons r s))
  have hparent : AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U)) hf (2 * p)
      (Open.SupportedLift.Constructions.Map.relativeClassMap V U (Set.range u) p (Open.SupportedLift.Constructions.restrictCycle V U (Set.range u) p c)) =
      Open.SupportedLift.Constructions.Map.relativeClassMap V U (Set.range u) p (Open.SupportedLift.Constructions.restrictCycle V U (Set.range u) p c) :=
    ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id (ModuleCat.of ℚ ℚ) (TopCat.of U) (Set.range u)ᶜ (2 * p)) _
  rw [hparent, BaseVectorNormal.Constructions.Class.vectorNormalClass_head_change (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU n r s a ha] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Vector.Constructions.Class
