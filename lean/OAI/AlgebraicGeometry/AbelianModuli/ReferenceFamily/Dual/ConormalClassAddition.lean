import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConormalSheafClass
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RegularPair.ClassAddition

/-! # Conormal Class Addition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConormalClassAddition

noncomputable section

/-! Evaluation of the actual deformation cocycle is additive in
the identity conormal vector, also after taking native sheaf classes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.CategoryTheory.MonObj

variable (X : Over (Spec (.of (DualNumber ℂ)))) [Smooth X.hom] [IsSeparated X.hom]
    [IsIntegral (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left]
    [Smooth (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).hom] [GrpObj (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)]
    (U : X.left.AffineOpenCover)

local instance dualConormalAdd_group :
    AddCommGroup (CategoryTheory.Sheaf.H (UnitCechClasses.ringAdditiveSheaf (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left.sheaf) 1) :=
  inferInstanceAs (AddCommGroup ((CategoryTheory.Sheaf.functorH
    (Opens.grothendieckTopology (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left.toPresheafedSpace.carrier) 1).obj
      (UnitCechClasses.ringAdditiveSheaf (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left.sheaf)))

theorem dualSpecialFiberRegularPair_add
    (z w : Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)) (i j : U.I₀) :
    ReducedCechCover.dualSpecialFiberRegularPair X U (z + w) i j =
      ReducedCechCover.dualSpecialFiberRegularPair X U z i j + ReducedCechCover.dualSpecialFiberRegularPair X U w i j :=
  (congrArg (DualAffine.RegularSections.dualAffineRegularSectionEquiv ℂ X (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j))
    ((DualAffine.ConormalCocycle.dualFamilyPairConormalTransition X U i j).map_add z w)).trans
      (map_add (DualAffine.RegularSections.dualAffineRegularSectionEquiv ℂ X (CommonOpenCocycle.dualFamilyPairAffineOpen ℂ X U i j)) _ _)

theorem dualConormalSheafClass_add
    (z w : Constructed.IdentityConormal.constructedIdentityConormal ℂ (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X)) :
    ConormalSheafClass.dualConormalSheafClass X U (z + w) = ConormalSheafClass.dualConormalSheafClass X U z + ConormalSheafClass.dualConormalSheafClass X U w := by
  let v := ReducedCechCover.dualSpecialFiberRegularPair X U z
  let v' := ReducedCechCover.dualSpecialFiberRegularPair X U w
  have hv := ReducedCechCover.dualSpecialFiberRegularPair_cocycle X U z
  have hv' := ReducedCechCover.dualSpecialFiberRegularPair_cocycle X U w
  have he : ReducedCechCover.dualSpecialFiberRegularPair X U (z + w) = (fun i j => v i j + v' i j) :=
    funext (fun i => funext (fun j => dualSpecialFiberRegularPair_add X U z w i j))
  exact (RegularPair.ClassAddition.regularPairSheafClass_congr (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left (ReducedCechCover.dualSpecialFiberCechCover X U)
    _ _ (ReducedCechCover.dualSpecialFiberCechCover_covers X U) (ReducedCechCover.dualSpecialFiberRegularPair_cocycle X U (z + w))
    (RegularPair.ClassAddition.regularPairCocycle_add (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left (ReducedCechCover.dualSpecialFiberCechCover X U) v v' hv hv') he).trans
      (RegularPair.ClassAddition.regularPairSheafClass_add (DualAffine.ConormalInclusions.dualFamilySpecialFiberObject ℂ X).left (ReducedCechCover.dualSpecialFiberCechCover X U)
        v v' (ReducedCechCover.dualSpecialFiberCechCover_covers X U) hv hv')

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.ConormalClassAddition
