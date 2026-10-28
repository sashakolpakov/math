import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference.IsogenyDifferential
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.DualPointLift

/-! # Dual Point Lifts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference

noncomputable section

/-! Every actual dual-number point at the lattice-dual origin lifts
through the constructed isogeny to an actual point at the original origin. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    {M : AlgebraicModel.ReferenceAlgebraicModel F hP} {N : DualModel.ReferenceDualModel F hP}

open OAI.RepresentationTheory.Theta.Geometric.Intrinsic.DualPointLift

local instance IsogenyKernel.ReferenceLatticeIsogeny.dualPointLift_integral (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : IsIntegral A.toOver.left := A.variety.property
local instance IsogenyKernel.ReferenceLatticeIsogeny.dualPointLift_smooth (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) : Smooth A.toOver.hom := A.variety.presentation.smooth

theorem IsogenyKernel.ReferenceLatticeIsogeny.exists_dualPoint_at_origin_lift (p : IsogenyKernel.ReferenceLatticeIsogeny M N)
    (q : DualOpen.Lifts.DualSchemePoints N.abelian.toOver 1) :
    ∃ r : DualOpen.Lifts.DualSchemePoints M.abelian.toOver 1, r.val ≫ p.nativeMap = q.val := by
  have hone : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.nativeMap (1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) = 1 :=
    MonObj.one_comp p.nativeMap
  let q' : DualOpen.Lifts.DualSchemePoints N.abelian.toOver
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p.nativeMap (1 : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) :=
    ⟨q.val, q.property.trans hone.symm⟩
  exact RepresentationTheory.Theta.Geometric.Intrinsic.DualPointLift.exists_nativeDualPoint_lift p.nativeMap 1 (p.mfderiv_bijective 1).surjective q'

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Reference
