import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.BlockPairingBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.PairingFibers
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.KernelParameterBaseChange

/-! # Choice Kernel Base Change -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.ChoiceKernelBaseChange.Construction

noncomputable section

/-! The canonical polarized CMPoints kernel commutes with actual parameter
pullback on arbitrary bases with universal global functions, with the original source polarization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable {E L : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field L] [NumberField L] {κ : L →+* ℂ} {q : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (iota : E →+* L) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme.{0}} {g : ℕ} (A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g S)
  (σ : AbelianModuli.ReferenceFamily.ActionData.IntegralAction (NumberField.RingOfIntegers E) A) (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)
  {δ : Fin g → ℕ} (pol : AbelianModuli.HilbertConstruction.PolarizationData.Polarization D δ) (hD : GlobalFunctions.Construction.HasUniversalGlobalFunctions D.abelian.scheme) (h s : ℕ) (labels : ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))
  (M : Fin s → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module (ZMod (q ^ h)) (M i)] [∀ i, Finite (M i)]
  (P : Over S)
  (U : ∀ i, SubgroupFunctor.Construction.SupportedChoice A.scheme (q ^ h) (M i) (CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ h s labels i) P)

def universalFunctionCMPointsChoiceKernel : TorsionQuotient.SubgroupFunctor.RelativeSubgroup A.scheme P :=
  ChoiceKernel.Construction.choiceFullKernel (q ^ h) s M
    (CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ h s labels)
    (CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ h s labels)
    (CM.PointsPerfectKernel.Construction.l45SourceBlockPairing j iota hsplit A σ h s labels
      (PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing A D pol hD (q ^ h) (pow_pos (Fact.out : q.Prime).pos h))) U

set_option backward.isDefEq.respectTransparency false in
theorem universalFunctionCMPointsChoiceKernel_parameterBaseChange :
    Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter (Grp.mk A.scheme) P
      (universalFunctionCMPointsChoiceKernel j iota hsplit A σ D pol hD h s labels M P U) =
    universalFunctionCMPointsChoiceKernel j iota hsplit (A.pullback P.hom) (σ.pullback P.hom)
      (D.pullback P.hom) (pol.pullback P.hom) (hD.pullback P.hom) h s labels M (Over.mk (𝟙 P.left))
      (KernelParameterBaseChange.Construction.blockChoicesOverParameter A P (q ^ h) s M (CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ h s labels) U) := by
  let c0 := PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing A D pol hD (q ^ h) (pow_pos (Fact.out : q.Prime).pos h)
  let c1 := PolarizationAdapter.Construction.universalFunctionNativePolarizationPairing (A.pullback P.hom) (D.pullback P.hom) (pol.pullback P.hom) (hD.pullback P.hom)
    (q ^ h) (pow_pos (Fact.out : q.Prime).pos h)
  let p := CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j iota hsplit A σ h s labels
  let r := CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j iota hsplit A σ h s labels
  let ep := CM.PointsPerfectKernel.Construction.l45SourceBlockPairing j iota hsplit A σ h s labels c0
  have hc : c1 = Intrinsic.TorsionPairingBaseChange.Construction.nativeTorsionPairingPullback P.hom (Grp.mk A.scheme) (Grp.mk A.scheme) (q ^ h) c0 :=
    PairingFibers.Construction.universalFunctionNativePolarizationPairing_baseChange D hD pol (q ^ h) (pow_pos (Fact.out : q.Prime).pos h) P.hom
  have hp : (fun i => Intrinsic.BlockPairingBaseChange.Construction.nativeBlockPairingPullback A (p i) (r i) (q ^ h) P.hom (ep i)) =
      CM.PointsPerfectKernel.Construction.l45SourceBlockPairing j iota hsplit (A.pullback P.hom) (σ.pullback P.hom) h s labels c1 := by
    funext i
    exact (CM.BlockPairingBaseChange.Construction.l45SourceBlockPairing_baseChange j iota hsplit A σ h s labels P.hom c0 i).symm.trans
      (congrArg (fun c => CM.PointsPerfectKernel.Construction.l45SourceBlockPairing j iota hsplit (A.pullback P.hom) (σ.pullback P.hom) h s labels c i)
        hc.symm)
  exact (KernelParameterBaseChange.Construction.choiceFullKernel_parameterBaseChange A P (q ^ h) s M p r ep U).trans
    (congrArg (fun e => ChoiceKernel.Construction.choiceFullKernel (q ^ h) s M
      (fun i => (Over.pullback P.hom).map (p i)) (fun i => (Over.pullback P.hom).map (r i)) e
      (KernelParameterBaseChange.Construction.blockChoicesOverParameter A P (q ^ h) s M p U)) hp)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UniversalFunction.ChoiceKernelBaseChange.Construction
