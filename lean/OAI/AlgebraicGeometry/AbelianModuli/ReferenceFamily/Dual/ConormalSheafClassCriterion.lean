import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConormalSheafClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassZeroCriterion

/-! # Conormal Sheaf Class Criterion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConormalSheafClassCriterion

noncomputable section

/-! The native degree-one conormal obstruction classes vanish
exactly when the actual varying family admits a normalized product. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.CategoryTheory.MonObj

attribute [local implicit_reducible] CommonOpenCocycle.dualFamilyPairAffineOpen ChartGauge.dualFamilyChartAffineOpen

variable (X : Over (Spec (.of (DualNumber ℂ)))) [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left]
    [Smooth (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).hom] [GrpObj (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)]
    (U : X.left.AffineOpenCover)

local instance dualConormalCriterion_addCommGroup :
    AddCommGroup (CategoryTheory.Sheaf.H (UnitCechClasses.ringAdditiveSheaf (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left.sheaf) 1) :=
  inferInstanceAs (AddCommGroup ((CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left.toPresheafedSpace.carrier) 1).obj
      (UnitCechClasses.ringAdditiveSheaf (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left.sheaf)))

theorem dualConormalSheafClass_zero_iff_scalarPrimitive
    (z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)) :
    ConormalSheafClass.dualConormalSheafClass X U z = 0 ↔
      ∃ a : ConormalBasisPrimitives.dualScalarGaugeParameters X U, ConormalBasisPrimitives.IsDualScalarConormalPrimitive X U z a := by
  constructor
  · exact ConormalSheafClass.dualScalarConormalPrimitive_of_sheafClass_zero X U z
  · rintro ⟨a, ha⟩
    let s (i : U.I₀) : Γ((DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left, ReducedCechCover.dualSpecialFiberCechCover X U i) :=
      DualAffine.RegularSections.dualAffineRegularSectionEquiv ℂ X (ChartGauge.dualFamilyChartAffineOpen ℂ X U i) (a i)
    have hs : RegularPair.Closed.RegularPairPrimitive (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left (ReducedCechCover.dualSpecialFiberCechCover X U)
        (ReducedCechCover.dualSpecialFiberRegularPair X U z) s := by
      intro i j
      have h := congrArg (DualAffine.RegularSections.dualAffineRegularSectionEquiv ℂ X (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j)) (ha i j)
      rw [map_sub, DualAffine.RegularSections.dualAffineRegularSectionEquiv_restrict, DualAffine.RegularSections.dualAffineRegularSectionEquiv_restrict] at h
      exact h
    exact (RegularPair.ClassZeroCriterion.regularPairSheafClass_eq_zero_iff_primitive (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left
      (ReducedCechCover.dualSpecialFiberCechCover X U) (ReducedCechCover.dualSpecialFiberRegularPair X U z) (ReducedCechCover.dualSpecialFiberCechCover_covers X U)
      (ReducedCechCover.dualSpecialFiberRegularPair_cocycle X U z)).mpr ⟨s, hs⟩

theorem normalizedDualProduct_iff_conormalSheafClasses_zero :
    (∃ e : X ≅ (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseProjection ℂ)).obj (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X),
      NormalizedDual.OpenProductData.NormalizesDualProductFiber ℂ e) ↔
    ∀ z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X), ConormalSheafClass.dualConormalSheafClass X U z = 0 := by
  constructor
  · intro he
    obtain ⟨v, hv⟩ := (ConormalBasisPrimitives.normalizedDualProduct_iff_conormalPrimitive X U).mp he
    intro z
    exact (dualConormalSheafClass_zero_iff_scalarPrimitive X U z).mpr
      ⟨fun i => v i z, fun i j => hv i j z⟩
  · exact ConormalSheafClass.normalizedDualProduct_of_conormalSheafClasses_zero X U

theorem conormalSheafClasses_zero_cover_independent (V : X.left.AffineOpenCover) :
    (∀ z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X), ConormalSheafClass.dualConormalSheafClass X U z = 0) ↔
    ∀ z : Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X), ConormalSheafClass.dualConormalSheafClass X V z = 0 :=
  (normalizedDualProduct_iff_conormalSheafClasses_zero X U).symm.trans
    (normalizedDualProduct_iff_conormalSheafClasses_zero X V)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConormalSheafClassCriterion
