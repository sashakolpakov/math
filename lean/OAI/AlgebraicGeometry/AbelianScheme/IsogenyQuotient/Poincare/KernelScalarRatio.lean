import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.KernelOriginCoordinates
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.FamilyExplicitRatio
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ParameterScalarProduct
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.ParameterKernelCharacter
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Kernel.CocycleOriginScalar

/-! # Kernel Scalar Ratio -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.KernelScalarRatio.Construction

noncomputable section

/-! The actual Poincare kernel cocycle is the ratio of the explicit
scalar frame at zero and the scalar frame at its original torsion point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.FrameUnits

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {Q : Over (Spec (.of k))} (t : Q ⟶ D.abelian.scheme) (n : ℕ) (ht : t ^ n = 1)

def poincareParameterOriginScalarFrame (U : Over Q.left) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.left ≅ Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
      (lift (KernelOriginCoordinates.Construction.poincareParameterDualCoordinate D t U) 1) :=
  ScalarFrameTarget.Construction.poincareTorsionScalarFrameTo D n (KernelOriginCoordinates.Construction.poincareParameterDualCoordinate D t U) 1
    (KernelOriginCoordinates.Construction.poincareParameterDualCoordinate_pow D t n ht U) _
    (congrArg (lift (KernelOriginCoordinates.Construction.poincareParameterDualCoordinate D t U)) (one_pow n))

def poincareParameterTorsionScalarFrame (U : Over Q.left)
    (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n))) :
    AbelianModuli.HilbertConstruction.Line.Bundles.structureModule U.left ≅ Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D)
      (lift (KernelOriginCoordinates.Construction.poincareParameterDualCoordinate D t U) 1) :=
  ScalarFrameTarget.Construction.poincareTorsionScalarFrameTo D n (KernelOriginCoordinates.Construction.poincareParameterDualCoordinate D t U)
    (KernelOriginCoordinates.Construction.poincareParameterKernelCoordinate n U z) (KernelOriginCoordinates.Construction.poincareParameterDualCoordinate_pow D t n ht U) _
    (congrArg (lift (KernelOriginCoordinates.Construction.poincareParameterDualCoordinate D t U)) (KernelOriginCoordinates.Construction.poincareParameterKernelCoordinate_pow n U z))

set_option backward.isDefEq.respectTransparency false in
theorem poincareParameterKernelCocycle_frameRatio [IsAffine Q.left] (U : Over Q.left)
    (z : U ⟶ Picard.Homomorphisms.Kernel.Construction.kernelScheme ((Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n))) :
    (ParameterKernelCharacter.Construction.poincareParameterKernelCocycle D n t ht).value 1 z =
      (Picard.PoincareBundle.Line.FrameUnits.frameRatio (poincareParameterOriginScalarFrame D t n ht U)
        (poincareParameterTorsionScalarFrame D t n ht U z) : Γ(U.left, ⊤)) := by
  let f := (Over.pullback Q.hom).map ((𝟙 A.scheme) ^ n)
  let a := z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f
  let p := Parameter.ProductPoints.Construction.parameterProductPoint Q A.scheme U (1 : U ⟶ (Over.pullback Q.hom).obj A.scheme)
  let q := Parameter.ProductPoints.Construction.parameterProductPoint Q A.scheme U a
  let τ := KernelOriginCoordinates.Construction.poincareParameterDualCoordinate D t U
  let r := lift τ (1 : (Over.map Q.hom).obj U ⟶ A.scheme)
  have h0 : (1 : U ⟶ (Over.pullback Q.hom).obj A.scheme) ≫ f = 1 := MonObj.one_comp f
  have hz : a ≫ f = 1 := by
    change (z ≫ Picard.Homomorphisms.Kernel.Construction.kernelInclusion f) ≫ f = 1
    rw [Category.assoc, Picard.Homomorphisms.KernelGroup.Construction.kernelInclusion_comp, MonObj.comp_one]
  have hp := ParameterScalarProduct.Construction.poincareParameterProductPoint_image n U 1 1 h0
  have hq := ParameterScalarProduct.Construction.poincareParameterProductPoint_image n U 1 a hz
  have hr := KernelOriginCoordinates.Construction.poincareParameterProduct_origin D t U
  have hpa : lift (p ≫ fst Q A.scheme ≫ t) ((p ≫ snd Q A.scheme) ^ n) = r :=
    (FamilyScalarFrame.Construction.poincareFamilyScalarPoint_comp D t n p).symm.trans
      ((FamilyScalarRatio.Construction.poincareFamilyScalarPoint_of_image D t n p p hp).trans hr)
  have hqa : lift (q ≫ fst Q A.scheme ≫ t) ((q ≫ snd Q A.scheme) ^ n) = r :=
    (FamilyScalarFrame.Construction.poincareFamilyScalarPoint_comp D t n q).symm.trans
      ((FamilyScalarRatio.Construction.poincareFamilyScalarPoint_of_image D t n p q hq).trans hr)
  have ep := ScalarFrameTarget.Construction.poincareTorsionScalarFrameTo_congr D n (p ≫ fst Q A.scheme ≫ t) τ
    (p ≫ snd Q A.scheme) 1 (FamilyScalarFrame.Construction.poincareFamilyDualCoordinate_pow D t n ht p)
    (KernelOriginCoordinates.Construction.poincareParameterDualCoordinate_pow D t n ht U) r hpa
    (congrArg (lift τ) (one_pow n))
    ((Category.assoc p (fst Q A.scheme) t).symm.trans
      (congrArg (fun b => b ≫ t) (Parameter.ProductPoints.Construction.parameterProductPoint_fst Q A.scheme U 1)))
    ((Parameter.ProductPoints.Construction.parameterProductPoint_snd Q A.scheme U 1).trans (map_one _))
  have eq := ScalarFrameTarget.Construction.poincareTorsionScalarFrameTo_congr D n (q ≫ fst Q A.scheme ≫ t) τ
    (q ≫ snd Q A.scheme) (KernelOriginCoordinates.Construction.poincareParameterKernelCoordinate n U z)
    (FamilyScalarFrame.Construction.poincareFamilyDualCoordinate_pow D t n ht q) (KernelOriginCoordinates.Construction.poincareParameterDualCoordinate_pow D t n ht U)
    r hqa (congrArg (lift τ) (KernelOriginCoordinates.Construction.poincareParameterKernelCoordinate_pow n U z))
    ((Category.assoc q (fst Q A.scheme) t).symm.trans
      (congrArg (fun b => b ≫ t) (Parameter.ProductPoints.Construction.parameterProductPoint_fst Q A.scheme U a)))
    (KernelOriginCoordinates.Construction.poincareParameterKernelCoordinate_product n U z)
  have hs := Kernel.CocycleOriginScalar.Construction.pullbackLineKernelCocycle_one_scalar f (TorsionParameterLine.Construction.poincareTorsionParameterLine D t)
    (TorsionParameterLine.Construction.poincareTorsionParameterPullbackFrame D t n ht).symm z
  exact hs.trans ((ParameterScalarProduct.Construction.poincareParameterDescentScalar_product D t n ht U 1 1 a h0 hz).trans
    ((FamilyExplicitRatio.Construction.poincareFamilyDescentScalar_explicit D t n ht p p q hp hq r hr).trans
      (congrArg Units.val (congrArg₂ Picard.PoincareBundle.Line.FrameUnits.frameRatio ep eq))))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.KernelScalarRatio.Construction
