import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ReducedCechCover
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.Closed
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConormalBasisPrimitives

/-! # Conormal Sheaf Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConormalSheafClass

noncomputable section

/-! The actual varying family determines ordinary degree-one sheaf
classes by evaluation on its constructed identity conormal module.
Vanishing of these native classes produces an actual normalized product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] CommonOpenCocycle.dualFamilyPairAffineOpen ChartGauge.dualFamilyChartAffineOpen

variable (X : Over (Spec (.of (DualNumber ℂ)))) [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left]
    [Smooth (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).hom] [GrpObj (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)]
    (U : X.left.AffineOpenCover)

def dualConormalSheafClass (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)) :
    CategoryTheory.Sheaf.H (UnitCechClasses.ringAdditiveSheaf (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left.sheaf) 1 :=
  RegularPair.Closed.regularPairSheafClass (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left (ReducedCechCover.dualSpecialFiberCechCover X U)
    (ReducedCechCover.dualSpecialFiberCechCover_covers X U) (ReducedCechCover.dualSpecialFiberRegularPair X U z)
    (ReducedCechCover.dualSpecialFiberRegularPair_cocycle X U z)

local instance dualConormalSheafClass_addCommGroup :
    AddCommGroup (CategoryTheory.Sheaf.H (UnitCechClasses.ringAdditiveSheaf (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left.sheaf) 1) :=
  inferInstanceAs (AddCommGroup ((CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left.toPresheafedSpace.carrier) 1).obj
      (UnitCechClasses.ringAdditiveSheaf (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left.sheaf)))

theorem dualScalarConormalPrimitive_of_sheafClass_zero
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X))
    (hz : dualConormalSheafClass X U z = 0) :
    ∃ a : ConormalBasisPrimitives.dualScalarGaugeParameters X U, ConormalBasisPrimitives.IsDualScalarConormalPrimitive X U z a := by
  obtain ⟨s, hs⟩ := RegularPair.Closed.regularPairPrimitive_of_sheafClass_zero (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left
    (ReducedCechCover.dualSpecialFiberCechCover X U) (ReducedCechCover.dualSpecialFiberRegularPair X U z) (ReducedCechCover.dualSpecialFiberCechCover_covers X U)
    (ReducedCechCover.dualSpecialFiberRegularPair_cocycle X U z) hz
  let a : ConormalBasisPrimitives.dualScalarGaugeParameters X U := fun i =>
    (DualAffine.RegularSections.dualAffineRegularSectionEquiv ℂ X (ChartGauge.dualFamilyChartAffineOpen ℂ X U i)).symm (s i)
  refine ⟨a, fun i j => ?_⟩
  apply (DualAffine.RegularSections.dualAffineRegularSectionEquiv ℂ X (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j)).injective
  rw [map_sub, DualAffine.RegularSections.dualAffineRegularSectionEquiv_restrict, DualAffine.RegularSections.dualAffineRegularSectionEquiv_restrict]
  have he (t : U.I₀) : DualAffine.RegularSections.dualAffineRegularSectionEquiv ℂ X (ChartGauge.dualFamilyChartAffineOpen ℂ X U t) (a t) = s t :=
    (DualAffine.RegularSections.dualAffineRegularSectionEquiv ℂ X (ChartGauge.dualFamilyChartAffineOpen ℂ X U t)).apply_symm_apply (s t)
  exact (hs i j).trans (congrArg₂ (· - ·)
    (congrArg ((DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left.presheaf.map
      (homOfLE ((VaryingDualReduction.dualFamilyReduction ℂ X).preimage_mono
        (show (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j).1 ≤ (ChartGauge.dualFamilyChartAffineOpen ℂ X U i).1 from inf_le_left))).op)
      (he i).symm)
    (congrArg ((DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left.presheaf.map
      (homOfLE ((VaryingDualReduction.dualFamilyReduction ℂ X).preimage_mono
        (show (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j).1 ≤ (ChartGauge.dualFamilyChartAffineOpen ℂ X U j).1 from inf_le_right))).op)
      (he j).symm))

theorem normalizedDualProduct_of_conormalSheafClasses_zero
    (hz : ∀ z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X), dualConormalSheafClass X U z = 0) :
    ∃ e : X ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).obj (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X),
      NormalizedDual.OpenProductData.NormalizesDualProductFiber ℂ e := by
  let b := Module.Free.chooseBasis ℂ (Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X))
  apply (ConormalBasisPrimitives.normalizedDualProduct_iff_basisPrimitives X U b).mpr
  intro t
  exact dualScalarConormalPrimitive_of_sheafClass_zero X U (b t) (hz (b t))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConormalSheafClass
