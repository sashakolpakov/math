import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ParameterKernels
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CorrespondenceFibers

/-! # Parameter Kernels -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.ParameterKernels

noncomputable section

/-! The native IsogenyQuotient representing object classifies actual chosen kernels
on every base test scheme. This is the full relative subgroup functor,
with each branch retained separately even when targets coincide. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.KernelChoice.CM

variable {E L K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field L] [NumberField L] {κ : L →+* ℂ} [Field K] [CharZero K]
  {q s g N : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (iota : E →+* L) (hsplit : j.HasSplitCoordinates iota)
  (M : Over (Spec (.of K)))
  (F : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N M.left)
  (n : ℕ) (labels : Fin s → Gal(E/ℚ)) (a : Fin s → Fin 3 → ℕ)
  [∀ v, Module (ZMod (q ^ n)) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v))]

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

abbrev nativeKernelFunctor : (Over M.left)ᵒᵖ ⥤ Type 1 :=
  AbelianScheme.IsogenyQuotient.Parameter.Products.Construction.blockTupleFunctor s (fun v => AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.supportedSubgroupFunctor F.abelian.scheme (q ^ n)
    (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)) (HeckeCycles.Intrinsic.KernelChoice.CM.projector j iota hsplit F n (labels v)))

variable (Q : Over M.left) (repr : (nativeKernelFunctor j iota hsplit M F n labels a).RepresentableBy Q)

def parameterFiberKernelEquiv (T : Over (Spec (.of K))) (x : T ⟶ M) :
    AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.SourceFiber (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M Q) x ≃
      AbelianScheme.TateComparison.Subgroups.KernelChoices (F.pullback x.left) (fun v => j.localCharacter iota (labels v)) n a :=
  (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterFiberEquiv M Q _ repr T x).trans
    ((AbelianScheme.IsogenyQuotient.Universal.Choices.Construction.blockTupleCoordinates s (fun v => AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.supportedSubgroupFunctor F.abelian.scheme (q ^ n)
      (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)) (HeckeCycles.Intrinsic.KernelChoice.CM.projector j iota hsplit F n (labels v)))
        (.op (Over.mk x.left))).trans
      (HeckeCycles.Intrinsic.ParameterKernels.CM.kernelEquiv j iota hsplit F M.hom (Over.mk x.left) n labels a))

def parameterBranchChoices (T : Over (Spec (.of K))) (x : T ⟶ M)
    (c : AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.SourceFiber (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M Q) x) :
    HeckeCycles.Intrinsic.ParameterKernels.CM.Parameters j iota hsplit F (Over.mk x.left) n labels a :=
  AbelianScheme.IsogenyQuotient.Universal.Choices.Construction.blockTupleCoordinates s (fun v => AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.supportedSubgroupFunctor F.abelian.scheme (q ^ n)
    (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v)) (HeckeCycles.Intrinsic.KernelChoice.CM.projector j iota hsplit F n (labels v)))
      (.op (Over.mk x.left)) (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterFiberEquiv M Q _ repr T x c)

theorem parameterFiberKernelEquiv_membership (T : Over (Spec (.of K))) (x : T ⟶ M)
    (c : AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.SourceFiber (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M Q) x) (v : Fin s)
    (U : Over T.left) (z : U ⟶ (F.pullback x.left).abelian.scheme) :
    z ∈ ((parameterFiberKernelEquiv j iota hsplit M F n labels a Q repr T x c).val v).atTest U ↔
      (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv x.left (Grp.mk F.abelian.scheme) U).symm z ∈
        (parameterBranchChoices j iota hsplit M F n labels a Q repr T x c v).val.subgroup.points
          ((Over.map x.left).obj U) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint (Over.mk x.left) U) :=
  HeckeCycles.Intrinsic.ParameterKernels.CM.kernelEquiv_membership j iota hsplit F M.hom
    (Over.mk x.left) n labels a (parameterBranchChoices j iota hsplit M F n labels a Q repr T x c) v U z

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.ParameterKernels
