import OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Vector

/-! # Vector Presentation -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorPresentation.Constructions

noncomputable section

/-! A cycle-vector class can be displayed in any exactly identified
pair of supports. The comparison is an actual invertible pair map,
and sends the original finite-cycle class to the same displayed class. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.Vector.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.Class OAI.AlgebraicGeometry.CycleClass.Thom.BaseVectorNormal.Constructions.SectionSupport OAI.AlgebraicGeometry.CycleClass.Thom.BaseSectionVector.Constructions
open OAI.AlgebraicGeometry.CycleClass.Thom.EvenIntersectionAssociativity.Constructions.SupportedCupTargets OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions.Map OAI.AlgebraicGeometry.CycleClass.Thom.Open.SupportedLift.Constructions OAI.AlgebraicGeometry.CycleClass.Thom.Normalization.GoodSmoothMap.Constructions.AffineOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)

local instance : IsIntegral V.toOver.left := inferInstanceAs (IsIntegral V.carrier)
local instance : Smooth V.toOver.hom := inferInstanceAs (Smooth V.structureMap)

variable (B : V.carrier.Opens) [Nonempty B] (U : Opens V.analyticSpace)
  (hU : (U : Set V.analyticSpace) ⊆ Set.range (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B)))
  {L : Type} (u : L → U) (n : ℕ) (s : Fin n → Γ((Normalization.GoodSmoothMap.Constructions.AffineOpen.affineBase B).left, ⊤))
  (S T : Set U) (hS : Set.range u = S) (hT : Set.range (BaseVectorNormal.Constructions.SectionSupport.vectorZeroImage (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU n s) = T)

include hS hT in
theorem present_mapsTo : Set.MapsTo (𝟙 (TopCat.of U)) (S ∩ T)ᶜ (Vector.Constructions.Class.vectorIntersectionSupport V B U hU u n s)ᶜ :=
  fun _ hx hy => hx ⟨hS ▸ hy.1, hT ▸ hy.2⟩

theorem present_injective (d : ℕ) : Function.Injective
    (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (present_mapsTo V B U hU u n s S T hS hT) d) := by
  cases hS
  cases hT
  rw [AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id]
  exact Function.injective_id

theorem present_cycleVectorClass (p d : ℕ) (hd : p + n = d) (hu : IsOpen (Set.range u)ᶜ)
    (hSC : IsOpen Sᶜ) (hTC : IsOpen Tᶜ) (hST : Sᶜ ∪ Tᶜ = (S ∩ T)ᶜ)
    (hg : Set.MapsTo (BaseSectionVector.Constructions.baseSectionVector (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU n s) Tᶜ ({0}ᶜ))
    (c : Geometric.DimensionCycles.RationalDimensionCycle V p) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (present_mapsTo V B U hU u n s S T hS hT) (2 * d)
      (Vector.Constructions.Class.cycleVectorClassAt V B U hU u p n d hd s hu c) =
    EvenIntersectionAssociativity.Constructions.SupportedCupTargets.cupTo (TopCat.of U) Sᶜ Tᶜ (S ∩ T)ᶜ hSC hTC hST (2 * p) (2 * n) (2 * d) (by omega)
      (Open.SupportedLift.Constructions.Map.relativeClassMap V U S p (Open.SupportedLift.Constructions.restrictCycle V U S p c))
      (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (BaseSectionVector.Constructions.baseSectionVector (Normalization.GoodSmoothMap.Constructions.AffineOpen.baseInclusion B) U hU n s) hg
        (2 * n) (Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass n)) := by
  cases hS
  cases hT
  exact ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id (ModuleCat.of ℚ ℚ) (TopCat.of U)
    (Vector.Constructions.Class.vectorIntersectionSupport V B U hU u n s)ᶜ (2 * d))
      (Vector.Constructions.Class.cycleVectorClassAt V B U hU u p n d hd s hu c)

theorem present_cycleClass (d : ℕ) (c : Geometric.DimensionCycles.RationalDimensionCycle V d) :
    AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomologyMap (ModuleCat.of ℚ ℚ) (𝟙 (TopCat.of U))
      (present_mapsTo V B U hU u n s S T hS hT) (2 * d)
      (Open.SupportedLift.Constructions.Map.relativeClassMap V U (Vector.Constructions.Class.vectorIntersectionSupport V B U hU u n s) d
        (Open.SupportedLift.Constructions.restrictCycle V U (Vector.Constructions.Class.vectorIntersectionSupport V B U hU u n s) d c)) =
    Open.SupportedLift.Constructions.Map.relativeClassMap V U (S ∩ T) d (Open.SupportedLift.Constructions.restrictCycle V U (S ∩ T) d c) := by
  cases hS
  cases hT
  exact ConcreteCategory.congr_hom (AlgebraicTopology.Cohomology.Singular.RelativeOpenSupport.relativeSingularCohomologyMap_id (ModuleCat.of ℚ ℚ) (TopCat.of U)
    (Vector.Constructions.Class.vectorIntersectionSupport V B U hU u n s)ᶜ (2 * d))
      (Open.SupportedLift.Constructions.Map.relativeClassMap V U (Vector.Constructions.Class.vectorIntersectionSupport V B U hU u n s) d
        (Open.SupportedLift.Constructions.restrictCycle V U (Vector.Constructions.Class.vectorIntersectionSupport V B U hU u n s) d c))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Cycle.VectorPresentation.Constructions
