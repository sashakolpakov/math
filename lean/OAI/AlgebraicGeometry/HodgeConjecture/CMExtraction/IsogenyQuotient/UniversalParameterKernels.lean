import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.ParameterKernels
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.ParameterKernelPullback

/-! # Universal Parameter Kernels -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.UniversalParameterKernels

noncomputable section

/-! Pullback of the represented universal tuple is precisely the kernel
tuple classified by each original source-fiber branch on every test. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.KernelChoice.CM

variable {E L K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [Field L] [NumberField L] {κ : L →+* ℂ} [Field K] [CharZero K]
  {q s g N : ℕ} [Fact q.Prime]
  (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (iota : E →+* L) (hsplit : j.HasSplitCoordinates iota)
  (M : Over (Spec (.of K)))
  (F : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) g N M.left)
  (h : ℕ) (labels : Fin s → Gal(E/ℚ)) (a : Fin s → Fin 3 → ℕ)
  [∀ v, Module (ZMod (q ^ h)) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v))]
  (Q : Over M.left) (repr : (ParameterKernels.nativeKernelFunctor j iota hsplit M F h labels a).RepresentableBy Q)

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩

abbrev representedChoices : HeckeCycles.Intrinsic.ParameterKernels.CM.Parameters j iota hsplit F Q h labels a :=
  AbelianScheme.IsogenyQuotient.Universal.Choices.Construction.universalBlockChoice (q ^ h) s (fun v => AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v))
    (fun v => HeckeCycles.Intrinsic.KernelChoice.CM.projector j iota hsplit F h (labels v)) repr

def representedKernels : AbelianScheme.TateComparison.Subgroups.KernelChoices (F.pullback Q.hom)
    (fun v => j.localCharacter iota (labels v)) h a :=
  HeckeCycles.Intrinsic.ParameterKernels.CM.kernelEquiv j iota hsplit F M.hom Q h labels a
    (representedChoices j iota hsplit M F h labels a Q repr)

omit [CharZero K] in
theorem representedChoices_at_branch (T : Over (Spec (.of K))) (x : T ⟶ M)
    (c : AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.SourceFiber (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M Q) x) :
    ParameterKernelPullback.nativeChoiceRestriction j iota hsplit F (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterFiberLiftEquiv M Q T x c) h labels a
      (representedChoices j iota hsplit M F h labels a Q repr) =
      ParameterKernels.parameterBranchChoices j iota hsplit M F h labels a Q repr T x c := by
  funext v
  apply Subtype.ext
  apply AbelianScheme.TorsionQuotient.SubgroupFunctor.SubgroupChoice.ext
  exact (AbelianScheme.IsogenyQuotient.Universal.Choices.Construction.universalBlockChoice_pullback (q ^ h) s (fun v => AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v))
    (fun v => HeckeCycles.Intrinsic.KernelChoice.CM.projector j iota hsplit F h (labels v)) repr
    (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterFiberLiftEquiv M Q T x c) v).symm

theorem representedKernels_at_branch (T : Over (Spec (.of K))) (x : T ⟶ M)
    (c : AbelianScheme.IsogenyQuotient.CorrespondenceFibers.Construction.SourceFiber (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterSource M Q) x) (v : Fin s) :
    let b : Over.mk x.left ⟶ Q := AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterFiberLiftEquiv M Q T x c
    (((representedKernels j iota hsplit M F h labels a Q repr).val v).pullback b.left).comapHom
      (AbelianScheme.TateComparison.BaseChangeCoherence.baseChangeFactorIso F.abelian b.left Q.hom x.left b.w).hom =
      (ParameterKernels.parameterFiberKernelEquiv j iota hsplit M F h labels a Q repr T x c).val v := by
  have hk := ParameterKernelPullback.parameterKernel_pullback j iota hsplit F M.hom
    (AbelianScheme.IsogenyQuotient.TotalParameters.Construction.totalParameterFiberLiftEquiv M Q T x c) h labels a
    (representedChoices j iota hsplit M F h labels a Q repr) v
  rw [representedChoices_at_branch] at hk
  exact hk

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.UniversalParameterKernels
