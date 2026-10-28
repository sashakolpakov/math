import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IsogenyDifferential
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.DualPointLift

/-! # Dual Point Lifts -/

namespace OAI.AlgebraicGeometry.Picard.ThetaConstruction

noncomputable section

/-! Every actual dual-number point at the lattice-dual origin lifts
through the constructed isogeny to an actual point at the original origin. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {dim : ℕ} {matrix : DefinitionsIntegral.IntegralMatrix dim}
    {F : DefinitionsIntegral.MarkedPolarizedTorus dim matrix}
    {M : PeriodModel.Geometric.AlgebraicPeriodModel F} {N : IntegralDualModel.Geometric.IntegralDualAlgebraicModel F}

open OAI.RepresentationTheory.Theta.Geometric.Intrinsic.DualPointLift

local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.dualPointLift_integral (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.dualPointLift_smooth (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny.exists_dualPoint_at_origin_lift (p : IntegralDualIsogenyKernel.Geometric.IntegralDualLatticeIsogeny M N)
    (q : AbelianModuli.ReferenceFamily.DualOpen.Lifts.DualSchemePoints N.abelian.toOver 1) :
    ∃ r : AbelianModuli.ReferenceFamily.DualOpen.Lifts.DualSchemePoints M.abelian.toOver 1, r.val ≫ p.nativeMap = q.val := by
  have hone : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.nativeMap (1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) = 1 :=
    MonObj.one_comp p.nativeMap
  let q' : AbelianModuli.ReferenceFamily.DualOpen.Lifts.DualSchemePoints N.abelian.toOver
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.nativeMap (1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
    ⟨q.val, q.property.trans hone.symm⟩
  exact RepresentationTheory.Theta.Geometric.Intrinsic.DualPointLift.exists_nativeDualPoint_lift p.nativeMap 1 (p.mfderiv_bijective 1).surjective q'

end

end OAI.AlgebraicGeometry.Picard.ThetaConstruction
