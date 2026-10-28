import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.ParameterPointCoherence
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ParameterKernels

/-! # Parameter Kernel Pullback -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.ParameterKernelPullback

noncomputable section

/-! The native parameter-to-kernel equivalence commutes with arbitrary
parameter restriction, using the same canonical family comparison as TateComparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.KernelChoice.CM

variable {E L K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field L] [NumberField L] {κ : L →+* ℂ} [Field K] [CharZero K]
  {q s g N : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (iota : E →+* L) (hsplit : j.HasSplitCoordinates iota)
  {S : Scheme} (F : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N S)
  (base : S ⟶ Spec (.of K)) {P Q : Over S} (c : P ⟶ Q)
  (h : ℕ) (labels : Fin s → Gal(E/ℚ)) (a : Fin s → Fin 3 → ℕ)
  [∀ v, Module (ZMod (q ^ h)) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v))]

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

def nativeChoiceRestriction
    (H : HeckeCycles.Intrinsic.ParameterKernels.CM.Parameters j iota hsplit F Q h labels a) :
    HeckeCycles.Intrinsic.ParameterKernels.CM.Parameters j iota hsplit F P h labels a :=
  fun v => (AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.supportedSubgroupFunctor F.abelian.scheme (q ^ h)
    (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)) (HeckeCycles.Intrinsic.KernelChoice.CM.projector j iota hsplit F h (labels v))).map c.op (H v)

theorem parameterKernel_pullback
    (H : HeckeCycles.Intrinsic.ParameterKernels.CM.Parameters j iota hsplit F Q h labels a) (v : Fin s) :
    (((HeckeCycles.Intrinsic.ParameterKernels.CM.kernelEquiv j iota hsplit F base Q h labels a H).val v).pullback
      c.left).comapHom (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso F.abelian c.left Q.hom P.hom c.w).hom =
      (HeckeCycles.Intrinsic.ParameterKernels.CM.kernelEquiv j iota hsplit F base P h labels a
        (nativeChoiceRestriction j iota hsplit F c h labels a H)).val v := by
  apply AbelianScheme.TateComparison.Subgroups.PointSubgroup.ext
  intro U
  ext z
  change (F.abelian.pullback Q.hom).baseChangePointsMulEquiv c.left U
      (z ≫ (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso F.abelian c.left Q.hom P.hom c.w).hom) ∈
        ((HeckeCycles.Intrinsic.ParameterKernels.CM.kernelEquiv j iota hsplit F base Q h labels a H).val v).atTest
          ((Over.map c.left).obj U) ↔ _
  have hQ := HeckeCycles.Intrinsic.ParameterKernels.CM.kernelEquiv_membership j iota hsplit F base Q h labels a H v
    ((Over.map c.left).obj U)
    ((F.abelian.pullback Q.hom).baseChangePointsMulEquiv c.left U
      (z ≫ (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso F.abelian c.left Q.hom P.hom c.w).hom))
  have hP := HeckeCycles.Intrinsic.ParameterKernels.CM.kernelEquiv_membership j iota hsplit F base P h labels a
    (nativeChoiceRestriction j iota hsplit F c h labels a H) v U z
  exact hQ.trans ((ParameterPointCoherence.parameter_factor_membership F.abelian c U z (H v).val.subgroup).trans hP.symm)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.ParameterKernelPullback
