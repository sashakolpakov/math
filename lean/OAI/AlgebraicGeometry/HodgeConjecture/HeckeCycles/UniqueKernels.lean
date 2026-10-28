import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BranchKernels
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.KernelChoiceIso
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UniqueFiberTransport
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.FineKernelData

/-! # Unique Kernels -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UniqueKernels.CM

noncomputable section

/-! The original fine-model kernel classification transfers to the
identical retained generic model through its actual branch equivalence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.IsogenyQuotient.FineKernelData
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.KernelAtLiftEquality.CM.Restricted

variable {E K K' : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] [Field K']
  {s N q : ℕ} [Fact q.Prime] {P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s} {iota : E →+* K}
  (M : AbelianModuli.ReferenceFamily.Models.FinePELModel P iota N) (p : Spec (.of K') ⟶ Spec (.of K))
  {X : Over (Spec (.of K'))} [IsReduced X.left] [IsLocallyNoetherian X.left]
  (e : X ≅ (Over.pullback p).obj (PELModuli.IntegralModel.Reduction.reduction M.space))
  (A : AbelianScheme.TateComparison.PEL.PELFamilyData (NumberField.RingOfIntegers E) (3 * s) N X.left)
  (eA : AbelianScheme.TateComparison.PELModuli.PELFamilyIso A ((CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M).pullback (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap p M.space e)))
  (C : AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence M.space) (t : AbelianScheme.TateComparison.Local.IntegralType s)
  (χ : Fin s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])
  (f : CMExtraction.IsogenyQuotient.FineKernelData.UniversalIsogeny (q := q) M C t)
  (hf : CMExtraction.IsogenyQuotient.FineKernelData.ClassifiesChosenKernels M C t χ f)

include hf in
theorem at_test (T : Over (Spec (.of K'))) (x : T ⟶ X)
    (H : AbelianScheme.TateComparison.Subgroups.KernelChoices (A.pullback x.left) (fun v => χ (v, false)) t.multiplierNat t.exponentNat) :
    ∃! c : T ⟶ (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M.space e C).cover,
      ∃ w : c ≫ (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M.space e C).source = x,
        ∀ v, KernelAtLiftEquality.CM.Restricted.atLift A (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M.space e C).source.left
          (BranchKernels.CM.kernel p M.space e (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M) A eA C f
            (χ (v, false)) t.multiplierNat)
          x.left c.left (congrArg (fun z => z.left) w) = H.val v := by
  let ex := PELRestrictionNaturality.CM.atPoint A (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M)
    (CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap p M.space e) eA x.left
  let x₀ := ReducedReferencePoint.CM.Reference.point p M.space e x
  let be := ReducedReferencePoint.CM.Reference.branchEquiv p M.space e x C
  let H₀ : CMExtraction.IsogenyQuotient.FineKernelData.chosenKernels M t χ x₀ :=
    KernelChoiceIso.CM.equivalence ex (fun v => χ (v, false)) t.multiplierNat t.exponentNat H
  let original := fun b : C.Fiber x₀ => fun v => CMExtraction.IsogenyQuotient.FineKernelData.chosenKernelAtLift M C t χ f x₀ b.val b.property v
  let retained := fun c : (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M.space e C).Fiber x => fun v =>
    KernelAtLiftEquality.CM.Restricted.atLift A (CMExtraction.ReducedCorrespondence.IsogenyQuotient.modelCorrespondence p M.space e C).source.left
      (BranchKernels.CM.kernel p M.space e (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M) A eA C f
        (χ (v, false)) t.multiplierNat) x.left c.val.left (congrArg (fun z => z.left) c.property)
  let tr := fun J : Fin s → AbelianScheme.TateComparison.Subgroups.PointSubgroup
    ((CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M).pullback (x.left ≫ CMExtraction.ReducedCorrespondenceSquares.IsogenyQuotient.originalSpaceMap p M.space e)).abelian =>
      fun v => (J v).comapHom ex.abelian.hom
  have ht : Function.Injective tr := by
    intro J L hJL
    funext v
    exact KernelAtLiftEquality.CM.comap_injective ex.abelian (congrFun hJL v)
  have hbranch : ∀ c, retained c = tr (original (be c)) := by
    intro c
    funext v
    exact BranchKernels.CM.at_branch p M.space e (CMExtraction.IsogenyQuotient.FineKernelData.fineFamily M) A eA C f
      (χ (v, false)) t.multiplierNat x c
  have htarget : tr H₀.val = H.val :=
    congrArg Subtype.val
      (KernelChoiceIso.CM.comap_inverse ex (fun v => χ (v, false)) t.multiplierNat t.exponentNat H)
  have hu : ∃! b : C.Fiber x₀, original b = H₀.val := by
    obtain ⟨b, ⟨hb, hk⟩, hu⟩ := hf.2 (Over.mk (T.hom ≫ p)) x₀ H₀
    refine ⟨⟨b, hb⟩, funext hk, ?_⟩
    intro c hc
    exact Subtype.ext (hu c.val ⟨c.property, fun v => congrFun hc v⟩)
  obtain ⟨c, hc, hu⟩ := UniqueFiberTransport.CM.of_equivalence be retained original tr ht hbranch H₀.val hu
  refine ⟨c.val, ⟨c.property, fun v => (congrFun hc v).trans (congrFun htarget v)⟩, ?_⟩
  rintro d ⟨hd, hk⟩
  have hd' : retained ⟨d, hd⟩ = tr H₀.val := (funext hk).trans htarget.symm
  exact congrArg Subtype.val (hu ⟨d, hd⟩ hd')

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.UniqueKernels.CM
