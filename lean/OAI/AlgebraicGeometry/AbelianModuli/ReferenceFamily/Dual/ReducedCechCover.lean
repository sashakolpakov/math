import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.RegularConormalCocycle
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Closed
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ChartGauge

/-! # Reduced Cech Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReducedCechCover

noncomputable section

/-! The actual affine cover induces a cover of the special fiber.
Its conormal transition values form a native regular Cech cocycle. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] ChartGauge.dualFamilyChartAffineOpen CommonOpenCocycle.dualFamilyPairAffineOpen CommonOpenCocycle.dualFamilyTripleAffineOpen
attribute [local implicit_reducible] DualAffine.RegularSections.dualAffineReducedOpen

variable (X : Over (Spec (.of (DualNumber ℂ)))) (U : X.left.AffineOpenCover)

def dualSpecialFiberCechCover (i : U.I₀) : (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left.Opens :=
  DualAffine.RegularSections.dualAffineReducedOpen ℂ X (ChartGauge.dualFamilyChartAffineOpen ℂ X U i)

theorem dualSpecialFiberCechCover_covers : iSup (dualSpecialFiberCechCover X U) = ⊤ := by
  apply top_unique
  intro x _
  apply Opens.mem_iSup.mpr
  refine ⟨U.idx (VaryingDualReduction.dualFamilyReduction ℂ X x), ?_⟩
  exact U.covers (VaryingDualReduction.dualFamilyReduction ℂ X x)

variable [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left]
    [Smooth (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).hom] [GrpObj (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)]

def dualSpecialFiberRegularPair (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X))
    (i j : U.I₀) :
    Γ((DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left, dualSpecialFiberCechCover X U i ⊓ dualSpecialFiberCechCover X U j) :=
  RegularConormalCocycle.dualRegularConormalTransition X U i j z

theorem dualSpecialFiberRegularPair_cocycle
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)) :
    RegularPair.Closed.RegularPairCocycle (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left (dualSpecialFiberCechCover X U)
      (dualSpecialFiberRegularPair X U z) :=
  fun i j l => RegularConormalCocycle.dualRegularConormalTransition_cocycle X U i j l z

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReducedCechCover
