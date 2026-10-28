import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.ParameterKernels
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.FineKernelData
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily

/-! # Fine Projectors -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.FineProjectors.CM

noncomputable section

/-! The original universal action gives exactly the native projectors
and subgroup functor after passage to TateComparison's family conventions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction

theorem exponentNat_antitone {s : ℕ} (t : AbelianScheme.TateComparison.Local.IntegralType s) (v : Fin s) :
    Antitone (t.exponentNat v) :=
  fun _ _ hij => Int.toNat_le_toNat (t.val.dominant v hij)

variable {E K L : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] [Field L] [NumberField L] {κ : L →+* ℂ}
  {s N q : ℕ} [Fact q.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N)

theorem action : AbelianScheme.TateComparison.PELAdapters.actionFromEnd (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M).action = M.universal.action :=
  PELFamily.CM.Family.actionFromEnd_toEnd M.universal.action

variable (j : PELModuli.CMPoints.Arithmetic.QadicChoice L κ q) (aE : E →+* L) (hsplit : j.HasSplitCoordinates aE)
  (h : ℕ) (labels : AbelianScheme.IsogenyQuotient.ChoiceKernel.Construction.KernelIndex s ≃ Gal(E/ℚ))

theorem chosen :
    AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j aE hsplit (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M).abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M).action)
      h s labels =
    AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j aE hsplit M.universal.polarized.abelian M.universal.action h s labels := by
  rw [CM.action]

theorem opposite :
    AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j aE hsplit (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M).abelian (AbelianScheme.TateComparison.PELAdapters.actionFromEnd (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M).action)
      h s labels =
    AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45OppositeProjectors j aE hsplit M.universal.polarized.abelian M.universal.action h s labels := by
  rw [CM.action]

theorem kernelFunctor (a : Fin s → Fin 3 → ℕ)
    [∀ v, Module (ZMod (q ^ h)) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v))] :
    CMExtraction.IsogenyQuotient.ParameterKernels.nativeKernelFunctor j aE hsplit M.space (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M) h (fun v => labels (.inl v)) a =
      AbelianScheme.IsogenyQuotient.Parameter.Products.Construction.blockTupleFunctor s (fun v => AbelianScheme.IsogenyQuotient.SubgroupFunctor.Construction.supportedSubgroupFunctor M.universal.polarized.abelian.scheme
        (q ^ h) (AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (a v))
        (AbelianScheme.IsogenyQuotient.CM.PointsIntrinsicFamily.Construction.l45ChosenProjectors j aE hsplit M.universal.polarized.abelian M.universal.action h s labels v)) := by
  unfold CMExtraction.IsogenyQuotient.ParameterKernels.nativeKernelFunctor Intrinsic.KernelChoice.CM.projector
  rw [CM.action]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.IsogenyQuotient.FineProjectors.CM
