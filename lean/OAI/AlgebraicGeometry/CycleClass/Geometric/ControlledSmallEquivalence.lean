import OAI.AlgebraicGeometry.CycleClass.Geometric.ControlledSmallificationMap
import OAI.AlgebraicGeometry.CycleClass.Geometric.SubspaceOperationLocality

/-! # Controlled Small Equivalence -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ControlledSmallEquivalence.Cycles

noncomputable section

/-!
# The support-controlled small-chain homotopy equivalence

The constructed ambient homotopy preserves small chains by its actual
subspace-image control. Restricting it supplies the second homotopy for the
support-controlled inverse of the genuine small-chain inclusion.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{0}) {J : Type} (U : J → Set X)
variable (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x : X, ∃ i, x ∈ U i)

/-- Every actual correction component preserves the small-chain image.
This uses spatial support control, without assuming naturality of the choices. -/
theorem smallificationHomotopyComponent_small (a b : ℕ)
    (c : (SmallChainImage.Cycles.integralSmallSingularChains X U).X a) :
    ControlledSmallificationMap.Cycles.smallificationHomotopyComponent X U hopen hcover a b
      ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f a c) ∈
      LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f b).hom := by
  by_cases hab : a + 1 = b
  · subst b
    rw [ControlledSmallificationMap.Cycles.smallificationHomotopyComponent_succ]
    exact SubspaceOperationLocality.Cycles.subspaceLocalOperation_preserves_smallChainImage X U
      (ControlledSmallification.Cycles.smallificationHomotopyDegree X U hopen hcover a)
      (fun A c hc => ControlledSmallification.Cycles.smallificationHomotopyDegree_subspace X U hopen hcover a A c hc)
      (LinearMap.mem_range_self _ c)
  · have hzero : ControlledSmallificationMap.Cycles.smallificationHomotopyComponent X U hopen hcover a b = 0 := by
      simp [ControlledSmallificationMap.Cycles.smallificationHomotopyComponent, hab]
    rw [hzero]
    exact (LinearMap.range ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f b).hom).zero_mem

/-- The same controlled homotopy restricts to the actual small-chain complex. -/
def smallificationSmallHomotopy :
    Homotopy (𝟙 (SmallChainImage.Cycles.integralSmallSingularChains X U))
      (SmallChainImage.Cycles.smallIntegralChainInclusion X U ≫ ControlledSmallificationMap.Cycles.smallificationChainMap X U hopen hcover) :=
  InjectiveHomotopyRestriction.Cycles.restrictHomotopy (SmallChainImage.Cycles.smallIntegralChainInclusion X U)
    (SmallChainImage.Cycles.smallIntegralChainInclusion_injective X U)
    (by simp) (by simp only [Category.assoc])
    (ControlledSmallificationMap.Cycles.smallificationAmbientHomotopy X U hopen hcover)
    (fun a b c => smallificationHomotopyComponent_small X U hopen hcover a b c)

/-- Inclusion recovers exactly the already support-controlled ambient homotopy. -/
@[reassoc]
theorem smallificationSmallHomotopy_inclusion (a b : ℕ) :
    (smallificationSmallHomotopy X U hopen hcover).hom a b ≫
        (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f b =
      (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f a ≫
        (ControlledSmallificationMap.Cycles.smallificationAmbientHomotopy X U hopen hcover).hom a b :=
  InjectiveHomotopyRestriction.Cycles.restrictedHomotopyComponent_comp _ _ _ _ a b

/-- The restricted correction has the identical ambient chain value. -/
theorem smallificationSmallHomotopy_apply_inclusion (a b : ℕ)
    (c : (SmallChainImage.Cycles.integralSmallSingularChains X U).X a) :
    (SmallChainImage.Cycles.smallIntegralChainInclusion X U).f b
        ((smallificationSmallHomotopy X U hopen hcover).hom a b c) =
      (ControlledSmallificationMap.Cycles.smallificationAmbientHomotopy X U hopen hcover).hom a b
        ((SmallChainImage.Cycles.smallIntegralChainInclusion X U).f a c) :=
  InjectiveHomotopyRestriction.Cycles.restrictedHomotopyComponent_apply _ _ _ _ a b c

/-- The genuine small-chain inclusion is a chain homotopy equivalence with
the constructed support-controlled inverse. -/
def controlledSmallChainHomotopyEquiv :
    HomotopyEquiv (SmallChainImage.Cycles.integralSmallSingularChains X U) (LocalHomology.Cycles.integralSingularChains X) where
  hom := SmallChainImage.Cycles.smallIntegralChainInclusion X U
  inv := ControlledSmallificationMap.Cycles.smallificationChainMap X U hopen hcover
  homotopyHomInvId := (smallificationSmallHomotopy X U hopen hcover).symm
  homotopyInvHomId := (ControlledSmallificationMap.Cycles.smallificationAmbientHomotopy X U hopen hcover).symm

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ControlledSmallEquivalence.Cycles
