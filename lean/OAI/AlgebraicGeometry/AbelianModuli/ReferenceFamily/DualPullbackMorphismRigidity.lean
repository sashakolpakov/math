import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.Product
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PullbackMorphismReduction
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ProperProductInfinitesimalRigidity

/-! # Dual Pullback Morphism Rigidity -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualPullbackMorphismRigidity

noncomputable section

/-! Actual relative maps between constant group families over dual
numbers are determined by their special fiber and identity section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable (A B : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj A] [GrpObj B]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]

theorem properDualPullbackMorphism_ext
    (f g : (Over.pullback (LieRanks.dualNumberTest ℂ).hom).obj A ⟶ (Over.pullback (LieRanks.dualNumberTest ℂ).hom).obj B)
    (hr : (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).map f = (Over.pullback (ReferenceFamily.Smooth.AffineDualProduct.dualBaseReduction ℂ)).map g)
    (he : η[(Over.pullback (LieRanks.dualNumberTest ℂ).hom).obj A] ≫ f =
      η[(Over.pullback (LieRanks.dualNumberTest ℂ).hom).obj A] ≫ g) : f = g := by
  apply (Pullback.Product.pullbackProductMorphismEquiv (LieRanks.dualNumberTest ℂ) A B).injective
  exact ProperProductInfinitesimalRigidity.properGroupDual_reduction_ext A B _ _
    (Dual.PullbackMorphismReduction.dualPullbackMorphismEquiv_reduction A B f g hr)
    (Pullback.Product.pullbackProductMorphismEquiv_identity_ext (LieRanks.dualNumberTest ℂ) A B f g he)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DualPullbackMorphismRigidity
